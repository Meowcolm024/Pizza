import Pizza

def main : IO Unit := do
  let stdin <- IO.getStdin
  IO.println "press ctrl+c to quit"
  while true do
    IO.print "> "
    let s <- stdin.getLine
    match parse s with
    | .ok r      => IO.println s!"Parse result: {r}"
    | .error err => IO.println s!"{err.msg}"
