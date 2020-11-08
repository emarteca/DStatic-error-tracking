## DStatic-error-tracking

QL re-implementation of the simple static analysis for identifying error-causing catch clauses presented as [Aspirator in OSDI 2014](https://www.eecg.utoronto.ca/~yuan/papers/failure_analysis_osdi14.pdf).

Specifically, it flags catch clauses if:
* catch block is empty or just contains a logging statement
* catch block contains TODO or FIXME in the comments
* catch catches a higher level exception like `Exception` and `Throwable` and also calls `abort` or `System.exit` (also looking for `halt`, although this was not in the original paper)

And, it does _not_ flag empty catch clauses if:
* catch block has a corresponding try that modifies the value of a local variable _and_ that variable is checked in the basic block after the catch
* catch block has a corresponding try that has `return`, `continue`, or `throw` as the last statement _and_ the basic block after the catch is not empty

### Tested with
Tested with a subset of the projects over which the original authors tested Aspirator. Specifically:
* [hbase](https://github.com/apache/hbase)
* [tomcat](https://github.com/apache/tomcat)

### Usage
1. [Install codeql](https://help.semmle.com/codeql/codeql-cli/procedures/get-started.html)
2. Download source code to analyze (or, directly download the QL database from [lgtm.com](https://lgtm.com/))
3. `./runQuery path_to_source projname findErrorCatch.ql`
4. Output will be `projname_temp.csv` 