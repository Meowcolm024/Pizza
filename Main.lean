import Pizza.Example

def main : IO Unit := do
  let stdin <- IO.getStdin
  IO.println "press ctrl+c to quit"
  while true do
    IO.print "> "
    let s <- stdin.getLine
    match Example.parse s with
    | .ok (s, r) => IO.println s!"Parse result: {s}\nRemaining: {r}"
    | .error err => IO.println s!"{err.msg}"
