type +'a hash_consed = { node : 'a; tag : int; hkey : int }
[@@deriving eq, show { with_path = false }]

let newtag =
  let r = ref ~-1 in
  fun () ->
    incr r;
    !r

module type HashedType = sig
  type t

  val equal : t -> t -> bool
  val hash : t -> int
end

module type Printable = sig
  type t

  val pp : Format.formatter -> t -> unit
end

module Printers = struct
  let pp_int ppf i = Format.fprintf ppf "%d" i

  let pp_list ?(pp_sep = fun ppf () -> Format.fprintf ppf "; ") ?(left = "[")
      ?(right = "]") pp ppf l =
    Format.fprintf ppf "%s%a%s" left Format.(pp_print_list ~pp_sep pp) l right

  let pp_array ?(pp_sep = fun ppf () -> Format.fprintf ppf "; ") ?(left = "[|")
      ?(right = "|]") pp ppf a =
    pp_list ~pp_sep ~left ~right pp ppf (Array.to_list a)
end

module HashTable (H : sig
  include HashedType
  include Printable with type t := t
end) : sig
  type t = {
    mutable table : H.t hash_consed Weak.t array;
    mutable blocks_size : int;
    mutable limit : int;
  }

  val create : int -> t
  val hashcons : t -> H.t -> H.t hash_consed
  val pp : Format.formatter -> t -> unit
end = struct
  type t = {
    mutable table : H.t hash_consed Weak.t array;
    mutable blocks_size : int;
    mutable limit : int;
  }

  let pp_weak ppf w =
    for i = 0 to Weak.length w - 1 do
      match Weak.get w i with
      | None -> Format.fprintf ppf " "
      | Some v -> Format.fprintf ppf "%a" (pp_hash_consed H.pp) v
    done

  let pp ppf { table; blocks_size; limit } =
    Format.fprintf ppf "@[<v 1>{table: %a;@ blocks_size: %d;@ limit: %d}]"
      Printers.(pp_array pp_weak)
      table blocks_size limit

  let next_size n = min ((3 * n / 2) + 3) (Sys.max_array_length - 1)

  let create size =
    let size = if size < 7 then 7 else size in
    let size =
      if size > Sys.max_array_length then Sys.max_array_length else size
    in
    let empty_block = Weak.create 0 in
    { table = Array.make size empty_block; blocks_size = 0; limit = 3 }

  let fold f t init =
    let rec fold_block i b accu =
      if i < Weak.length b then
        fold_block (i + 1) b
          (match Weak.get b i with Some v -> f v accu | None -> accu)
      else accu
    in
    Array.fold_right (fold_block 0) t.table init

  let rec resize t =
    let len = Array.length t.table in
    let new_len = next_size len in

    if new_len > len then (
      let new_table = create new_len in
      new_table.limit <- t.limit + 100;
      fold (fun d () -> add new_table d) t ();
      t.table <- new_table.table;
      t.limit <- t.limit + 2)

  and add t d =
    let index = d.hkey mod Array.length t.table in
    let block = t.table.(index) in
    let size = Weak.length block in

    let rec search i =
      if i < size then
        if Weak.check block i then search (i + 1) else Weak.set block i (Some d)
      else
        let new_size = min (size + 3) (Sys.max_array_length - 1) in

        if new_size <= size then failwith "Not enought space"
        else
          (* Crée un nouveau block vide *)
          let new_block = Weak.create new_size in

          (* Recopie le block *)
          Weak.blit block 0 new_block 0 size;
          (* Ajoute le nouvel élément *)
          Weak.set new_block i (Some d);

          t.table.(index) <- new_block;
          t.blocks_size <- t.blocks_size + (new_size - size);

          if t.blocks_size > t.limit * Array.length t.table then resize t
    in
    search 0

  and hashcons t d =
    let hkey = H.hash d land max_int in
    let index = hkey mod Array.length t.table in
    let block = t.table.(index) in
    let size = Weak.length block in

    let rec search i =
      if i < size then
        match Weak.get_copy block i with
        | Some v when H.equal v.node d -> (
            match Weak.get block i with Some v -> v | None -> search (i + 1))
        | _ -> search (i + 1)
      else
        let n = { hkey; tag = newtag (); node = d } in
        add t n;
        n
    in
    search 0

  let _clear t =
    let empty_block = Weak.create 0 in
    for i = 0 to Array.length t.table - 1 do
      t.table.(i) <- empty_block
    done;
    t.blocks_size <- 0;
    t.limit <- 3
end

module PArray = struct
  type 'a t = {
    data : 'a data ref;
    default : 'a option;
    default_f : (int -> 'a) option;
  }

  and 'a data = Array of 'a array ref | Diff of int * 'a * 'a t

  let rec pp ppv ppf t = Format.fprintf ppf "%a" (pp_data ppv) !(t.data)

  and pp_data ppv ppf = function
    | Array a -> Format.fprintf ppf "Array %a" (Printers.pp_array ppv) !a
    | Diff (i, v, t) ->
        Format.fprintf ppf "Diff (%d, %a, %a)" i ppv v (pp ppv) t

  let create n v =
    {
      data = ref (Array (ref (Array.make n v)));
      default = Some v;
      default_f = None;
    }

  let init n f =
    {
      data = ref (Array (ref (Array.init n f)));
      default = None;
      default_f = Some f;
    }

  let rec reroot ({ data; _ } as t) =
    match !data with
    | Diff (i, v, t') -> (
        reroot t';
        let diff_data = !(t'.data) in
        match diff_data with
        | Array ref_a ->
            let v' = !ref_a.(i) in
            !ref_a.(i) <- v;
            data := diff_data;
            t'.data := Diff (i, v', t)
        | _ -> assert false)
    | Array _ -> ()

  let get t i =
    reroot t;
    match !(t.data) with
    | Array ref_a ->
        if i < 0 || i >= Array.length !ref_a then
          invalid_arg (Printf.sprintf "get %d" i);
        !ref_a.(i)
    | _ -> assert false

  let expand t prev_length new_length =
    match (t.default, t.default_f, !(t.data)) with
    | Some v, None, Array ref_a ->
        let a = Array.make new_length v in
        Array.blit !ref_a 0 a 0 prev_length;
        a
    | None, Some f, Array ref_a ->
        let a = Array.init new_length f in
        Array.blit !ref_a 0 a 0 prev_length;
        a
    | _ -> assert false

  let set t i v =
    if i < 0 then invalid_arg (Printf.sprintf "set %d" i);
    reroot t;
    match !(t.data) with
    | Array ref_a as data -> (
        let alength = Array.length !ref_a in
        let a, old =
          if i >= alength then (
            let a = expand t alength (max (alength * 2) i) in
            Array.unsafe_set a i v;
            (a, None))
          else
            let old = Array.unsafe_get !ref_a i in
            (!ref_a, if old == v then None else Some old)
        in
        ref_a := a;
        match old with
        | None -> t
        | Some old ->
            a.(i) <- v;
            let res = { t with data = ref data } in
            t.data := Diff (i, old, res);
            res)
    | _ -> assert false

  let ( = ) a1 a2 =
    let a1, a2 =
      match (!(a1.data), !(a2.data)) with
      | Array a1, Array a2 -> (!a1, !a2)
      | _ ->
          reroot a1;
          let a1 =
            match !(a1.data) with
            | Array a1 -> Array.copy !a1
            | _ -> assert false
          in
          reroot a2;
          let a2 =
            match !(a2.data) with
            | Array a2 -> Array.copy !a2
            | _ -> assert false
          in
          (a1, a2)
    in
    Stdlib.Array.for_all2 (fun a b -> a == b) a1 a2

  let ( != ) a1 a2 =
    let a1, a2 =
      match (!(a1.data), !(a2.data)) with
      | Array a1, Array a2 -> (!a1, !a2)
      | _ ->
          reroot a1;
          let a1 =
            match !(a1.data) with
            | Array a1 -> Array.copy !a1
            | _ -> assert false
          in
          reroot a2;
          let a2 =
            match !(a2.data) with
            | Array a2 -> Array.copy !a2
            | _ -> assert false
          in
          (a1, a2)
    in
    Stdlib.Array.exists2 (fun a b -> a <> b) a1 a2
end

module PUnion = struct
  type t = { mutable father : int PArray.t; rank : int PArray.t }

  let pp ppf t =
    Format.fprintf ppf "{father: %a; rank: %a}"
      PArray.(pp Printers.pp_int)
      t.father
      PArray.(pp Printers.pp_int)
      t.rank

  let create n =
    { rank = PArray.create n 0; father = PArray.init n (fun i -> i) }

  let rec find_aux father i =
    let fi = PArray.get father i in
    if fi = i then (father, i)
    else
      let f, r = find_aux father fi in
      let f = PArray.set f i r in
      (f, r)

  let find h x =
    let f, rx = find_aux h.father x in
    h.father <- f;
    rx

  let equiv h x y =
    let rep_x = find h x in
    let rep_y = find h y in
    rep_x = rep_y

  let union h x y =
    let rep_x = find h x in
    let rep_y = find h y in
    if rep_x = rep_y then h
    else
      let rank_x = PArray.get h.rank rep_x in
      let rank_y = PArray.get h.rank rep_y in
      if rank_x > rank_y then
        { h with father = PArray.set h.father rep_y rep_x }
      else if rank_x < rank_y then
        { h with father = PArray.set h.father rep_x rep_y }
      else
        {
          rank = PArray.set h.rank rep_x (rank_x + 1);
          father = PArray.set h.father rep_y rep_x;
        }

  let ( = ) t1 t2 = PArray.(t1.father = t2.father) && PArray.(t1.rank = t2.rank)

  let ( != ) t1 t2 =
    PArray.(t1.father != t2.father) || PArray.(t1.rank != t2.rank)
end
