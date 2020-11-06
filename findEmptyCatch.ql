import java

bindingset[cStartLine, cStartCol, tcStartLine,tcStartCol]
predicate startContained(int tcStartLine, int tcStartCol, int cStartLine, int cStartCol) {
	cStartLine < tcStartLine or 
      		(cStartLine = tcStartLine and cStartCol < tcStartCol)
}

bindingset[cEndLine, cEndCol, tcEndLine,tcEndCol]
predicate endContained(int tcEndLine, int tcEndCol, int cEndLine, int cEndCol) {
	cEndLine > tcEndLine or 
      		(cEndLine = tcEndLine and cEndCol > tcEndCol)
}

predicate emptyBlock(Block b) {
	b.getNumStmt() = 0
}

predicate catchHasOnlyLogging(CatchClause cc) {
	forall( Expr c | c.getAnEnclosingStmt() = cc.getBlock().getAStmt() | 
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
predicate catchHasBadExit(CatchClause cc) {
	exists( Call c | c = cc.getBlock().getAStmt() and c.getCallee().getName() = "abort")
	or
	hasSystemExitMethod(cc.getBlock())
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
predicate catchHasBadComment(CatchClause c) {
	exists( JavadocText jdc | jdc.getFile() = c.getFile() and 
				 (jdc.getText().matches("%TODO%") or jdc.getText().matches("%FIXME%")) and 
				 startContained(jdc.getLocation().getStartLine(), jdc.getLocation().getStartColumn(), 
				 	c.getLocation().getStartLine(), c.getLocation().getStartColumn()) and
				 endContained(jdc.getLocation().getEndLine(), jdc.getLocation().getEndColumn(), 
				 	c.getLocation().getEndLine(), c.getLocation().getEndColumn())) 
}

predicate isBadCatch(CatchClause c) {
  emptyBlock( c.getBlock()) or
  catchHasOnlyLogging( c) or
  catchHasBadComment( c) or
  (catchHasGeneralException(c) and catchHasBadExit(c))  
}

from CatchClause c
// where exists(JavadocText jdc | jdc.getFile() = c.getBlock().getFile() and 
				 // (jdc.getText().matches("%TODO%") or jdc.getText().matches("%FIXME%"))and 
				 // //locContained(jdc.getLocation(), c.getLocation()))
				 // startContained(jdc.getLocation().getStartLine(), jdc.getLocation().getStartColumn(), 
				 // 	c.getLocation().getStartLine(), c.getLocation().getStartColumn()))
// where isBadCatch(c)
where isBadCatch(c)
select c, c.getFile(), c.getLocation()