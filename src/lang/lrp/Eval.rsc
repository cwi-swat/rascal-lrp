module lang::lrp::Eval


import lang::lrp::Syntax;
import lang::javascript::EvalJS;
import DateTime;
import String;
import ParseTree;
import IO;


/*

- variables only initialized at the very beginning
- active machine/state list should be a tree (or array of stacks when concurrency only at toplevel)
  (assume state names are unique)
- reset timers indeed before onEntry
- make identification of machine/state stuff location independent

*/

// there's no shadowing so the whole state 
// can be represented as a single map 
alias Heap = map[str var, value val];

alias Timers = rel[str from, str to, datetime now];

alias Active = tuple[str state, Timers timers];

alias Thread = list[Active]; // stack 

alias RT = tuple[map[str machine, Thread thread] threads, Heap heap];

// Helper functions

void run(loc l, int delay = 1000) {
  run(parse(#start[LRP], l), delay = delay);
}

void run(start[LRP] lrp, int delay = 1000) {
  rt = initialize(lrp);
  while (true) {
    rt = loop(lrp, rt);
    sleep(delay);
  }
}



// System-wide functions

RT initialize(start[LRP] lrp) {
  RT rt = <(), initVars(lrp)>;
  for ((Code)`spawn <Id x> <Id s>` <- lrp.top.spawns) {
    str m = "<x>";
    <rt.threads[m], rt.heap> = makeActive(lookupMachine(lrp, m), "<s>", rt.heap);
  }
  return rt;    
}

RT loop(start[LRP] lrp, RT rt) {
  for (str tid <- rt.threads) {
    <rt.threads[tid], rt.heap> = fire(lookupMachine(lrp, tid), rt.threads[tid], rt.heap);
  }
  return rt;
} 


// Per thread functions

tuple[Thread, Heap] makeActive(Machine m, str state, Heap heap) {
  Timers timers = initTimers(m);
  <nested, heap> = onEntry(lookupState(m, state), heap);
  return <[<state, timers>] + nested, heap>;
}

tuple[Thread, Heap] fire(Machine m, Thread me, Heap heap) {
  Decl current = lookupState(m, me[0].state);
  if (Decl t <- outgoing(m, current), evalGuard(t, m, heap)) {
    heap = onExit(current, me, heap);
    return makeActive(m, "<t.to>", heap);
  }
  return running(current, me, heap);
}


bool evalGuard(Decl trans, Machine m, Thread me, Heap heap) {
  if (trans is epsilon) {
    return true;
  }
  
  if ((Decl)`on time <Expression t> <Id from> -\> <Id to>` := trans, int delta := evalJS("<t>", heap).val) {
    datetime started = lookupTimer(me[0].timers, from, to);
    return now() > incrementMilliseconds(started, delta);
  }
  
  // Covers both wildcard and ordinary transitions
  if ((Decl)`event <Id e> <Expression cond>;` <- m.decls, e == trans.event) {
    return (bool b := evalJS("<cond>", heap).val) && b;
  }
  
  throw "invalid transition <trans>";
}


tuple[Thread, Heap] onEntry(Decl state, Heap heap) {
  list[Contents] cs = contentsOf(state);

  if ((Contents)`on entry {<Statement* js>}` <- cs) {
    return <[], evalJS("{<js>}", heap).bindings>;
  }
  
  if ((Contents)`on entry spawn <Id m> <Id s>` <- cs) {
    return makeActive(lookupMachine(parent, m), "<s>", heap);
  }

  return <[], heap>;
}


tuple[Thread, Heap] running(Decl state, Thread me, Heap heap) {
  assert me[0].state == "<state.name>";
  
  for ((Contents)`running {<Statement* js>}` <- contentsOf(state)) {
    heap = evalJS("{<js>}", heap).bindings;
  } 
  
  // NB: this really depends on uniqueness of state names across machines
  if ((Contents)`<Machine m>` <- contentsOf(state), hasChild(m, me)) {
    <nested, heap> = fire(m, me[1..], heap);
    return <[me[0], *nested], heap>;
  } 
  
  return <me, heap>;
}


Heap onExit(Decl state, Thread me, Heap heap) {
  if ((Contents)`<Machine m>` <- contentsOf(state), hasChild(m, me)) {
    heap = onExit(lookupState(m, me[1].state), m[1..], heap);
  } 
  
  for ((Contents)`on exit {<Statement* js>}` <- contentsOf(state)) {
    heap = evalJS("{<js>}", heap).bindings;
  }
  
  return heap;
}

// Utils

list[Contents] contentsOf((State)`state <Id _> {<Contents* cs>}`) = [ c | Contents c <- cs ];

default list[Contents] contentsOf(State s) = [s.contents];

Heap initVars(start[LRP] lrp) 
  = ( () | it +  ("<x>": evalJS("<e>", it).val) | /(Decl)`var <Id x> := <Expression e>;` := lrp ); 

Timers initTimers(Machine m) 
  = { <"<from>", "<to>", now()> |  (Decl)`on time <Expression _> <Id from> -\> <Id to>` <- m.decls };

datetime lookupTimer(Timers ts, Id from, Id to) = dt
  when <str f, str t, datetime dt> <- ts, "<from>" ==f, "<to>" == t;

list[Decl] outgoing(Machine m, Decl s)
  = [ d | Decl d <- m.decls, (d has from && d.from == s.name) || d is wildcard ];

Machine lookupMachine(start[LRP] lrp, str tid) = m
  when Machine m <- lrp.top.machines, "<m.name>" == tid;

bool hasState(Machine m, str name) 
  = Decl s <- m.decls && s is state && "<s.name>" == name;

Decl lookupState(Machine m, str name) = s
  when Decl s <- m.decls, s is state, "<s.name>" == name;

bool hasChild(Machine m, Thread me) = size(me) > 1 && hasState(m, m[1].state);


