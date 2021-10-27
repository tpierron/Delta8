# Every planar graph with Delta = 8 is totally 10-choosable

This repository contains some programs that check the proofs from https://arxiv.org/abs/1904.12060.

- Delta8_check.mw is a Maple code checking proofs using Combinatorial Nullstellensatz.
- 7vertices.ml and 8vertices.ml are OCaml programs checking (exhaustively) that vertices of degree 7 or 8 end with non-negative weight after the discharging procedure.  Computation time is of the order of minutes on a standard computer.

# Running the programs

- Delta8_check.mw can be directly opened with Maple.
- The .ml files can be compiled and run with 

      ocamlopt -o file file.ml && ./file
 
