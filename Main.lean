import Pizza

def main : IO Unit := do
  let stdin <- IO.getStdin
  IO.println "press ctrl+c to quit"
  while true do
    IO.print "> "
    let s <- stdin.getLine
    IO.println s!"Parse result: {runParser s}"
