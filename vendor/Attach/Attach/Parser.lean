import Lean

open Lean Parser
namespace Attach

/-- Store a block verbatim. Commands following a block must start at or to the
left of `proof_of`; continuation lines are indented. Strings, character literals, and nested comments
are skipped lexically, so command-looking text inside them is harmless. -/
def rawProof : Parser where
  fn := fun c s => Id.run do
    let start := s.pos
    let anchor := c.fileMap.toPosition (c.savedPos?.getD start)
    let mut p := start
    let mut depth := 0
    let mut quoted := false
    let mut escaped := false
    let mut lineComment := false
    while !c.atEnd p do
      let ch := c.get p
      let next := c.next p
      let ch' := if c.atEnd next then '\x00' else c.get next
      if lineComment then
        if ch == '\n' then lineComment := false
      else if quoted then
        if escaped then escaped := false
        else if ch == '\\' then escaped := true
        else if ch == '"' then quoted := false
      else if depth > 0 then
        if ch == '/' && ch' == '-' then
          depth := depth + 1
          p := next
        else if ch == '-' && ch' == '/' then
          depth := depth - 1
          p := next
      else
        let pos := c.fileMap.toPosition p
        if pos.line > anchor.line && pos.column ≤ anchor.column && !ch.isWhitespace then
          break
        if ch == '\'' then
          let close := c.next next
          if ch' == '\\' then
            let mut q := c.next close
            while !c.atEnd q && c.get q != '\'' && c.get q != '\n' do
              q := c.next q
            if !c.atEnd q && c.get q == '\'' then p := q
          else if !c.atEnd close && c.get close == '\'' then p := close
        else if ch == '"' then quoted := true
        else if ch == '-' && ch' == '-' then lineComment := true
        else if ch == '/' && ch' == '-' then
          depth := 1
          p := next
      p := c.next p
    let text := c.extract start p
    let info := SourceInfo.original "".toRawSubstring start "".toRawSubstring p
    return (s.setPos p).pushSyntax (.atom info text)

@[combinator_parenthesizer rawProof] def rawProof.parenthesizer : Lean.PrettyPrinter.Parenthesizer := Lean.PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter rawProof] def rawProof.formatter : Lean.PrettyPrinter.Formatter := Lean.PrettyPrinter.Formatter.visitAtom Name.anonymous

syntax (name := proofBlock) withPosition("proof_of " ident " := " rawProof) : command
syntax (name := unsupportedTermination) "termination_by " term : command
syntax (name := unsupportedDecreasing) "decreasing_by " tacticSeq : command
syntax (name := helperDecl) "helper " command : command
syntax (name := attachedDecl) declModifiers "attached " "theorem " declId declSig : command
syntax (name := bodilessDecl) declModifiers "theorem " declId declSig : command

end Attach
