-- The pascal code for all the different node types is rather
-- repetitive. One way to deal with this repetiton is to generate
-- the pascal code from a template, and that's what we'll do here.

-- Each item here corresponds to a class, representing a syntax node.
KINDS = {
   {'Syntax', 'Object', {}},
   {'Expr', 'Syntax', {}},
   {'BoolExpr', 'Expr', {}},
   {'Stmt', 'Syntax', {}},
   {'IfStmt', 'Stmt', {
       {'condition','BoolExpr'},
       {'thenPart', 'Stmt'},
       {'elsePart', 'Stmt'} }},
   {'WhileStmt', 'Stmt', {
       {'condition', 'BoolExpr'},
       {'body', 'Stmt'}}},
   {'WriteStmt', 'Stmt', {} }, -- TODO: arguments to WriteStmt
   {'AssignStmt', 'Stmt', {} }, -- TODO: arguments to AssignStmt
}


-- writing text with indentation -------------------------------------

LEVEL = 0

-- write a line at given indentation level
function wln(...)
   io.write(string.rep('  ',LEVEL))
   io.write(...)
   io.write('\n')
end

-- indent and dedent:
function ind()
   LEVEL = LEVEL + 1
end

function ded()
   LEVEL = LEVEL - 1
end


-- generators for pascal code ----------------------------------------

function signature(kind)
   local class, super, members = kind[1], kind[2], kind[3]
   local result = 'function New' ..  class .. '('
   for i,mem in pairs(members) do
      mName, mType = mem[1], mem[2]
      result = result .. mName .. ': T' .. mType
      if i < #members then result = result .. '; '
      else end
   end
   return result .. ')' .. ' : T' .. class  .. ';'
end

function constructors(kinds, with_body)
   ind()
   for i,kind in pairs(kinds) do
      wln(signature(kind))
      -- for now, just return nil (the empty pointer)
      if with_body then wln('  begin result := nil end;\n') end
   end
   ded()
end

function generate(kinds)
   wln('{$mode delphi}')
   wln('unit uAST; // abstract syntax tree for simple interpreter')
   wln('interface')
   wln()
   wln('type')
   wln('  Node     = ^NodeData;')
   wln('  NodeKind = ( kWRITE, kINT, kIF, kASSIGN, kBLOCK );')
   wln('  NodeData = record')
   wln('    case kind : NodeKind of')
   wln('      kINT    : ( vInt  : integer );')
   wln('      kWRITE  : ( vExpr : Node );')
   wln('end;')

   -- this chunk just declares a bunch of types and sets them all
   -- to be the same as the type Node (just for now, so it compiles)
   ind(); wln('type '); ind()
   for i,kind in pairs(kinds) do
      wln('T', kind[1], ' = Node;')
   end; ded(); ded()
   wln()

   constructors(kinds, false)
   wln()
   wln('implementation')
   wln()
   constructors(kinds, true)

   wln('end.')
end

-- main --------------------------------------------------------------

if not package.loaded['nodes'] then
   generate(KINDS)
end
