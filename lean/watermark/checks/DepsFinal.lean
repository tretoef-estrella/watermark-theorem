import RequestProject.Watermark.W7
open Lean Elab Command

partial def collect (env : Environment) (n : Name) (acc : NameSet) : NameSet := Id.run do
  if acc.contains n then return acc
  let mut acc := acc.insert n
  match env.find? n with
  | none => return acc
  | some ci =>
    for c in ci.getUsedConstantsAsSet.toList do
      acc := collect env c acc
    return acc

elab "#deps " id:ident : command => do
  let env ← getEnv
  let s := collect env id.getId {}
  let mut mods : Std.HashMap Name Nat := {}
  let mut total := 0
  for n in s.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if (`RequestProject).isPrefixOf m then
        total := total + 1
        mods := mods.insert m (mods.getD m 0 + 1)
    | none => pure ()
  logInfo m!"project decls in cone: {total}; modules: {mods.size}"
  for (m, c) in mods.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    logInfo m!"{m} {c}"

#deps Watermark.watermark_theorem
