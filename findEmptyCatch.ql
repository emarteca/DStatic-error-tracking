import java

predicate locContained(Location toCheck, Location cont) {
 	(cont.getStartLine() < toCheck.getStartLine() or 
      		(cont.getStartLine() = toCheck.getStartLine() and cont.getStartColumn() < toCheck.getStartColumn()))
  and 
  	(cont.getEndLine() > toCheck.getEndLine() or 
      		(cont.getEndLine() = toCheck.getEndLine() and cont.getEndColumn() > toCheck.getEndColumn()))
  and 
  cont.getFile() = toCheck.getFile()
}

predicate emptyBlock(Block b) {
	b.getNumStmt() = 0
}

predicate blockHasOnlyLogging(Block b) {
	forall( Expr c | c.getAnEnclosingStmt() = b.getAStmt() | 
					c instanceof MethodAccess and 
					c.(MethodAccess).getMethod().getQualifiedName().matches("PrintStream.print%")) // gets System.out.print (and ..ln)
}


predicate isSystemMethod(Method m) {
	m.getDeclaringType().hasQualifiedName("java.lang", "System") or m.getDeclaringType().hasQualifiedName("java.lang", "Runtime")
}

predicate isExitMethod(Method m) {
	m.hasName("exit") or m.hasName("halt")
}

predicate hasSystemExitMethod(Block b) {
	exists( MethodAccess mc, Method m | 
				m = mc.(MethodAccess).getMethod() and 
				mc.getAnEnclosingStmt() = b.getAStmt() and 
			    isExitMethod(m) and 
			    isSystemMethod(m))
}

// bad exits: System.exit or abort
predicate blockHasBadExit(Block b) {
	exists( Call c | c = b.getAStmt() and c.getCallee().getName() = "abort")
	or
	hasSystemExitMethod(b)
}

predicate catchHasGeneralException(CatchClause c) {
  exists(string typeName | 
	  (typeName = "Throwable" or typeName = "Exception") and
	  c.getACaughtType().hasQualifiedName("java.lang", typeName) and
	  // Check that all exceptions thrown in the try block are
	  // either more specific than the caught type or unrelated to it.
	  not exists(Type et | et = getAThrownExceptionType(c.getTry()) |
	    et.(RefType).getASubtype*().hasQualifiedName("java.lang", typeName)
	  )
  )
}


// taken from ExceptionCatch.ql  in examples of bad practice
private Type getAThrownExceptionType(TryStmt t) {
  exists(MethodAccess ma, Exception e |
    t.getBlock() = ma.getEnclosingStmt().getEnclosingStmt*() and
    ma.getMethod().getAnException() = e and
    result = e.getType()
  )
  or
  exists(ClassInstanceExpr cie, Exception e |
    t.getBlock() = cie.getEnclosingStmt().getEnclosingStmt*() and
    cie.getConstructor().getAnException() = e and
    result = e.getType()
  )
  or
  exists(ThrowStmt ts |
    t.getBlock() = ts.getEnclosingStmt*() and
    result = ts.getExpr().getType()
  )
}


// bad comment == one with TODO or FIXME 
predicate blockHasBadComment(Block b) {
	exists( JavadocText jdc | (jdc.getText().matches("%TODO%") or jdc.getText().matches("%FIXME%")) and locContained(jdc.getLocation(), b.getLocation())) 
}

predicate isBadCatch(CatchClause c) {
  emptyBlock( c.getBlock()) or
  blockHasOnlyLogging( c.getBlock()) or
  // blockHasBadComment( c.getBlock()) or
  (catchHasGeneralException(c) and blockHasBadExit(c.getBlock()))  
}

from CatchClause c
where isBadCatch(c)
// (jdc.getText().matches("%TODO%") or jdc.getText().matches("%FIXME%")) and locContained(jdc.getLocation(), c.getBlock().getLocation())
select c, c.getFile(), c.getLocation()