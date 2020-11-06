##TODO

We're first re-implementing the simple static analysis for identifying error-causing catch clauses presented as Aspirator in OSDI 2014.
Specifically, it emits warnings if:
* catch block is empty or just contains a logging statement
* catch block contains TODO or FIXME in the comments
* catch catches a higher level exception like `Exception` and `Throwable` and also calls `abort` or `System.exit`

And, it does _not_ emit a warning if:
* an empty catch block has a corresponding try that modifies the value of a local variable _and_ that variable is checked in the basic block after the catch
* an empty catch block has a corresponding try that has `return`, `continue`, or `throw` as the last statement _and_ the basic block after the catch is not empty
