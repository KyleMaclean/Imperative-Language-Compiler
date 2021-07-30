A standard Haskell script and a literate Haskell script are provided; they contain the same code and comments.

Compile with GHC then call `exec (comp (fac 10))` to compile and execute the example factorial program with an input of 10. The output shows the state of the virtual machine's memory upon termination; the variable `A` contains the value `3628800`, which is `10!`.
