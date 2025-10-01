use ascent::ascent;
ascent! {
   relation edge(i32, i32);
   relation path(i32, i32);

   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}

fn main() {
    let mut prog = AscentProgram::default();
    prog.edge = vec![(1, 2), (2, 3)];
    prog.run();
    println!("path: {:?}", prog.path);
}

// How do I use ascent to represent the CEK Machine
// Using Datalog as a pattern matcher
// How do I transfer the environment
// Common Subexpression Elimination when we have pure functions that repeat.
// Study LL Parsers indepth. (How FIRST, FOLLOW are calculated with \epsilon) -> FOllow is which actual characters appear after parsing a non terminal($ or end of stream included when start symbol -> this gets propagated down if say E end of S and F end of E).
//This thursday is the exam.
// Study it today.
// Today will be racket + some notes on Ascent
// Also implement the 3 joins in Rust
// L(1) or L(k) -> rewrite the grammar to have no nulls
// Get the free text of Siek book from the URL
// ask who bound a variable ? -> uniquify (use def chain?)

//irs.rkt from P2
// gensym -> racket fun that takes any symbol takes it and makes a new symbol that is not present in the intern table.
// |+889|
//
