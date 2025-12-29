include Kernel
module Printing = Printing
module Derived = Derived
module Elaborator = Elaborator
module Inductive = Inductive
module Parse = Parse
module Tast = Tast
module Tactic = Tactic
module Proof = Proof

let elaborate = Elaborator.parse_and_elaborate
