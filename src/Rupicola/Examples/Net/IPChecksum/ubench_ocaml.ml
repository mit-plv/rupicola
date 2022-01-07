let _WARMUP = 10
let _TRIALS = 11
let _COOLDOWN = 1
let _LAPS = _WARMUP + _TRIALS + _COOLDOWN

let testdata =
  let ch = open_in_bin "testdata.bin" in
  let bs = really_input_string ch (in_channel_length ch) in
  close_in ch;
  Bytes.of_string bs

let byte_listdata =
  List.of_seq (Bytes.to_seq testdata)

let version =
  Sys.argv.(1)

let bench name fn input =
  (* print_string name; print_newline (); flush_all (); *)
  let laptimes = Array.make (_LAPS + 1) Int64.zero in

  for i = 0 to _LAPS - 1 do
    laptimes.(i) <- Ocaml_intrinsics.Perfmon.rdtsc ();
    ignore (fn input);
  done;
  laptimes.(_LAPS) <- Ocaml_intrinsics.Perfmon.rdtsc ();

  for i = 0 to _LAPS - 1 do
    laptimes.(i) <- Int64.sub laptimes.(i + 1) laptimes.(i)
  done;

  Printf.printf "('ip_checksum', 'ocaml-%s', 'ocamlopt-%s', [" name version;
  print_string @@ Int64.to_string laptimes.(_WARMUP);
  for i = _WARMUP + 1 to _WARMUP + _TRIALS - 1 do
    print_string ", ";
    print_string @@ Int64.to_string laptimes.(i);
  done;
  print_string "]),\n";
  flush stdout

let must = function
  | Some x -> x
  | None -> failwith "must"

let spec_naive_cast =
  fun b -> b |> Char.code |> Z.of_int |> Ip_spec_naive.of_nat |> must

let impl_naive_cast =
  fun b -> b |> Char.code |> Z.of_int |> Ip_impl_naive.of_nat |> must

let () =
  (* bench "spec-naive" Ip_spec_naive.ip_checksum *)
  (*   (List.map spec_naive_cast byte_listdata); *)
  (* bench "impl-naive" Ip_impl_naive.ip_checksum_impl *)
  (*   (List.map impl_naive_cast byte_listdata); *)
  bench "spec-extr" Ip_spec_opt.ip_checksum
    byte_listdata;
  (* bench "impl-extr" Ip_impl_opt.ip_checksum_impl *)
  (*   byte_listdata *)
