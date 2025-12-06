(*
This module contains code for 'quote' and 'splice', the two main functions enabling reflection in the object language.

Reflection will be achieved by mirroring the hol language types (term, type, etc) inside the object language itself as
a 1:1 mapping. When the interpreter finds a call to 'quote', it will treat it as a piece of HOL code in memory, rather than
the value itself. So a 'quote (t : term)' will be evaluated as (t : rterm) representing the data as a member of the object language.

Splice does the opposite of this. When the interpreter encounters it at runtime, it will interpret it as a 'term' of the meta language (ocaml)
instead.

Since all of this is done before anything goes to the kernel, we don't have to worry about breaking the logic.
 *)
