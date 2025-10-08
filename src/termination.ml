(* termination.ml *)

(* compiles with ocaml-base-compiler.5.3.0 *)
(* compile command:
 *   ocamlopt -o termination termination.ml && ./termination 
 *)

module Async : sig

  type 'a promise

  val async : ?name:string -> (unit -> 'a) -> 'a promise
  val await : 'a promise -> 'a

  val run : (unit -> unit) -> unit

end = struct

  open Effect
  open Effect.Deep

  type 'a status =
    | Waiting of ('a -> unit) list
    | Done of 'a

  type 'a promise = {
    owner : string option;
    mutable status : 'a status;
  }

  let get_done_val p =
    match p.status with
    | Waiting _ -> assert false
    | Done y -> y

  let get_waiting_list p =
    match p.status with
    | Waiting ks -> ks
    | Done _ -> assert false

  type 'a async_arg = {
    name : string option;
    task : unit -> 'a
  }

  type _ Effect.t += Async : 'a async_arg -> ('a promise) t
  type _ Effect.t += Await : 'a promise -> 'a t

  let async ?name task = perform (Async {name; task})
  let await p = perform (Await p)

  let make_promise ?owner () = {owner; status = Waiting []}

  let run main =
    let ready = Queue.create() in
    let next() = if not (Queue.is_empty ready) then (Queue.take ready) () in
    let rec fulfil : type a. a promise -> a async_arg -> unit = fun p arg ->
      match arg.task() with
      (* Handling of [Async]: *)
      | effect Async arg', k ->
          (* Print name of task that has been spawned. *)
          begin match arg'.name with None -> () | Some name ->
            Printf.printf "  Running '%s' asynchronously.\n" name
          end;

          let p' = make_promise ?owner:(arg'.name) () in
          Queue.add (fun () -> continue k p') ready;
          fulfil p' arg'

      (* Handling of [Await]: *)
      | effect Await p', k ->
          (* Print name of [p']'s owner. *)
          begin match p'.owner with None -> () | Some owner ->
            Printf.printf "  Awaiting '%s' ... " owner;
          end;

          begin match p'.status with
          | Done v ->
              (* Print status of the promise [p']. *)
              begin match p'.owner with None -> () | Some owner ->
                Printf.printf "Done awaiting!'%s'.\n" owner;
              end;
              continue k v
          | Waiting ks ->
              (* Print status of the promise [p']. *)
              begin if Option.is_some p'.owner then
                Printf.printf "(its promise was not fulfiled).\n"
              end;
              let k' = fun v -> continue k v in
              p'.status <- Waiting (k' :: ks);
              next()
          end
      | y ->
          (* Execution of the task has finished. *)
          begin match arg.name with None -> () | Some name ->
            Printf.printf "  Finished running '%s'.\n" name;
          end;

          let ks = get_waiting_list p in
          List.iter (fun k -> Queue.add (fun () -> k y) ready) ks;
          p.status <- Done y;
          next()
    in    
    let p = make_promise ~owner:"main" () in
    fulfil p {name = (Some "main"); task = main}

end

(* Example 1. *)
let _ =
  Printf.printf "Example 1 (Should print 'Result = 6')\n";
  let open Async in
  let main() =
    let p1 = async ~name:"p1" (fun () -> 1) in
    let p2 = async ~name:"p2" (fun () ->
      let p3 = async ~name:"p3" (fun () ->
        let p4 = async ~name:"p4" (fun () -> 1 + await p1) in p4
      )
      in
      let p4 = await p3 in
      let p5 = async ~name:"p5" (fun () -> await p4 + await p1) in
      let p6 = async ~name:"p6" (fun () -> await p4) in
      await p6 + await p5
    )
    in
    Printf.printf "  Result = %d\n" (await p1 + await p2);
  in
  run main;
  Printf.printf "Successful termination!\n"

(* Example 2. *)
let _ =
  Printf.printf "\nExample 2 (Shows example from Appendix C.2.2 terminates)\n";
  let open Async in
  let yield() = let _ = async ~name:"yield" (fun () -> ()) in () in
  let main() =
    let r = ref None in
    let rec f() =
      match !r with
      | None -> yield(); f()
      | Some p -> await p
    in
    let p = async ~name:"f" f in
    r := Some p;
    await p;
    let rec diverge() = diverge() in diverge()
  in
  run main;
  Printf.printf "Successful termination!\n"

