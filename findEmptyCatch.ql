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

predicate badBlock(Block b) {
  // empty 
  b.getNumStmt() = 0 or
  // only logging
  forall( Stmt c | c = b.getAStmt() | c instanceof Call and (c.(Call).getCallee().getName().matches("%print%"))) or
  // comment with TODO or FIXME 
  exists( JavadocText jdc | (jdc.getText().matches("%TODO%") or jdc.getText().matches("%FIXME%")) and locContained(jdc.getLocation(), b.getLocation())) 
}

from CatchClause c, JavadocText jdc
where badBlock(c.getBlock())
// (jdc.getText().matches("%TODO%") or jdc.getText().matches("%FIXME%")) and locContained(jdc.getLocation(), c.getBlock().getLocation())
select c, c.getFile(), c.getLocation()