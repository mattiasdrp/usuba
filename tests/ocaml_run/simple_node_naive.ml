

let id x = x

let node1_ (x_) = 
    let x_ = x_ in 
    (x_)


let main x_stream = 
    Stream.from
    (fun _ -> 
    try
        let x_ = Stream.next x_stream in
        let (x_1) = (Int64.logand (Int64.shift_right x_ 0) Int64.one = Int64.one) in
        let (ret1) = node1_ ((x_1)) in
        let (x_') = (Int64.logor Int64.zero (if ret1 then (Int64.shift_left Int64.one 0) else Int64.zero))
        in Some (x_')
    with Stream.Failure -> None)
