module lang::lrp::Syntax

extend lang::javascript::saner::Syntax;

start syntax LRP 
  = Decl!machine!state!event!trans!wildcard!epsilon!timed* globals 
    Machine machine
    Code!js spawn
    ;
syntax Machine = @Foldable machine: "machine" Id name "{" Decl* decls "}" ;

syntax Decl
  = state: "state" Id name Contents contents 
  | event: "event" Id name Expression cond ";"
  | trans: "on" Id event Id from "-\>" Id to 
  | wildcard: "on" Id event "*" "-\>" Id to
  | epsilon: "on" Id from "-\>" Id to
  | timed: "on" "time" Expression time Id from "-\>" Id to
  | var: "var" Id name ":=" Expression init ";"
  ;

syntax Contents
  = machine: Machine machine
  | entry: "on" "entry" Code code
  | exit: "on" "exit" Code code
  | running: "running" Code!spawn code
  | @Foldable block: "{" Contents* contents "}"
  | empty: ";"
  ;
  
  
syntax Code 
  = js: "{" Statement* statements "}"
  | spawn: "spawn" Id machine Id initial 
  ;

syntax Expression 
  = robot: "robot"
  | cond: Expression!cond cond "?" Expression!cond then ":" Expression elseExp
  > 
  assoc (
    Id param "=\>" Expression body
   | "(" {Id ","}* params ")" "=\>" Expression body
  )
  | "(" {Id ","}* params ")" "=\>" Statement!empty!varDecl!expression
  | Id param "=\>" Statement!empty!varDecl!expression
  ;

keyword Reserved = "robot";


