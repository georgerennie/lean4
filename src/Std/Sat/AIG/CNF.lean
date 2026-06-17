/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.CNF
public import Std.Sat.AIG.Lemmas
import Init.ByCases
import Init.Omega

/-!
This module contains an implementation of a verified Tseitin transformation on AIGs. The key results
are the `toCNF` function and the `toCNF_equisat` correctness statement. The implementation is
done in the style of section 3.4 of the AIGNET paper.
-/

namespace Std
namespace Sat

namespace AIG

namespace Decl

/--
Produce a Tseitin style CNF for a `Decl.false`, using `output` as the tree node variable.
-/
def falseToCNF (output : Nat) : CNF Nat :=
  .empty |>.add [(output, .false)]

/--
Produce a Tseitin style CNF for a `Decl.atom`, using `output` as the tree node variable.
-/
def atomToCNF (output : Nat) (atom : Nat) : CNF Nat :=
  CNF.empty
    |>.add [(output, true), (atom, .false)]
    |>.add [(output, .false), (atom, true)]

def gatePosToCNF (output : Nat) (lhs rhs : Nat) (linv rinv : Bool) : CNF Nat :=
  CNF.empty
    |>.add [(output, .false), (lhs, !linv)]
    |>.add [(output, .false), (rhs, !rinv)]

def gateNegToCNF (output : Nat) (lhs rhs : Nat) (linv rinv : Bool) : CNF Nat :=
  CNF.empty
    |>.add [(output, true),  (lhs, linv), (rhs, rinv)]

def itePosToCNF (output : Nat) (cond ifTrue ifFalse : Nat) (cinv tinv finv : Bool) : CNF Nat :=
  CNF.empty
    |>.add [(cond, cinv), (ifTrue, !tinv), (output, .false)]
    |>.add [(cond, !cinv), (ifFalse, !finv), (output, .false)]

def iteNegToCNF (output : Nat) (cond ifTrue ifFalse : Nat) (cinv tinv finv : Bool) : CNF Nat :=
  CNF.empty
    |>.add [(cond, cinv), (ifTrue, tinv), (output, true)]
    |>.add [(cond, !cinv), (ifFalse, finv), (output, true)]

@[simp]
theorem falseToCNF_eval :
    (falseToCNF output).eval assign
      =
    (assign output == .false) := by
  simp [falseToCNF]

@[simp]
theorem atomToCNF_eval :
    (atomToCNF output a).eval assign
      =
    (assign output == assign a) := by
  simp only [atomToCNF, CNF.eval_add, CNF.Clause.eval_cons, beq_false, beq_true,
    CNF.Clause.eval_nil, Bool.or_false, CNF.eval_empty, Bool.and_true]
  cases assign output <;> cases assign a <;> decide

-- This ensures output is still false when it should be
@[simp]
theorem gatePosToCNF_eval :
    (gatePosToCNF output lhs rhs linv rinv).eval assign
      =
    decide ((((assign lhs) ^^ linv) && ((assign rhs) ^^ rinv)) ≥ assign output) := by
  simp [gatePosToCNF]
  generalize assign lhs = l
  generalize assign rhs = r
  generalize assign output = o
  decide +revert

-- This ensures output is still true when it should be
@[simp]
theorem gateNegToCNF_eval :
    (gateNegToCNF output lhs rhs linv rinv).eval assign
      =
    decide ((((assign lhs) ^^ linv) && ((assign rhs) ^^ rinv)) ≤ assign output) := by
  simp [gateNegToCNF]
  generalize assign lhs = l
  generalize assign rhs = r
  generalize assign output = o
  decide +revert

theorem gateToCNF_eval :
    ((gatePosToCNF output lhs rhs linv rinv) ++ (gateNegToCNF output lhs rhs linv rinv)).eval assign
      =
    (assign output == (((assign lhs) ^^ linv) && ((assign rhs) ^^ rinv))) := by
  simp [gatePosToCNF_eval, gateNegToCNF_eval]
  generalize assign lhs = l
  generalize assign rhs = r
  generalize assign output = o
  decide +revert

@[simp]
theorem itePosToCNF_eval {cond ifTrue ifFalse cinv tinv finv assign} :
    (itePosToCNF output cond ifTrue ifFalse cinv tinv finv).eval assign
      =
    decide
      ((ite ((assign cond) ^^ cinv) ((assign ifTrue) ^^ tinv) ((assign ifFalse) ^^ finv)) ≥
        assign output) := by
  simp [itePosToCNF]
  generalize assign output = o
  generalize assign cond = c
  generalize assign ifTrue = t
  generalize assign ifFalse = f
  decide +revert

@[simp]
theorem iteNegToCNF_eval {cond ifTrue ifFalse cinv tinv finv assign} :
    (iteNegToCNF output cond ifTrue ifFalse cinv tinv finv).eval assign
      =
    decide
      ((ite ((assign cond) ^^ cinv) ((assign ifTrue) ^^ tinv) ((assign ifFalse) ^^ finv)) ≤
        assign output) := by
  simp [iteNegToCNF]
  generalize assign output = o
  generalize assign cond = c
  generalize assign ifTrue = t
  generalize assign ifFalse = f
  decide +revert

theorem iteToCNF_eval {cond ifTrue ifFalse cinv tinv finv assign} :
    ((itePosToCNF output cond ifTrue ifFalse cinv tinv finv) ++
      (iteNegToCNF output cond ifTrue ifFalse cinv tinv finv)).eval assign
      =
    (assign output == ite ((assign cond) ^^ cinv) ((assign ifTrue) ^^ tinv) ((assign ifFalse) ^^ finv)) := by
  simp [itePosToCNF_eval, iteNegToCNF_eval]
  generalize assign output = o
  generalize assign cond = c
  generalize assign ifTrue = t
  generalize assign ifFalse = f
  decide +revert

end Decl

namespace toCNF

/--
Mix:
1. An assignment for AIG atoms
2. An assignment for auxiliary Tseitin variables
into an assignment that can be used by a CNF produced by our Tseitin transformation.
-/
def mixAssigns {aig : AIG Nat} (assign1 : Nat → Bool) (assign2 : Fin aig.decls.size → Bool)
    (var : Nat) : Bool :=
  if h : var < aig.decls.size then
    assign2 ⟨var, h⟩
  else
    assign1 (var - aig.decls.size)

/--
Project the atom assignment out of a CNF assignment
-/
def projectLeftAssign (aig : AIG Nat)  (assign : Nat → Bool) : Nat → Bool :=
  fun var => assign (var + aig.decls.size)

/--
Project the auxiliary variable assignment out of a CNF assignment
-/
def projectRightAssign (assign : Nat → Bool) :
    (idx : Nat) → Bool := fun idx => assign idx

@[simp]
theorem projectLeftAssign_property :
    (projectLeftAssign aig assign) x = (assign (x + aig.decls.size)) := by
  simp [projectLeftAssign]

@[simp]
theorem projectRightAssign_property :
    (projectRightAssign assign) x = (assign x) := by
  simp [projectRightAssign]

/--
Given an atom assignment, produce an assignment that will always satisfy the CNF generated by our
Tseitin transformation. This is done by combining the atom assignment with an assignment for the
auxiliary variables, that just evaluates the AIG at the corresponding node.
-/
def cnfSatAssignment (aig : AIG Nat) (assign1 : Nat → Bool) : Nat → Bool :=
  mixAssigns assign1 (fun idx => ⟦aig, ⟨idx.val, false, idx.isLt⟩, assign1⟧)

@[simp]
theorem satAssignment_inl : (cnfSatAssignment aig assign1) (x + aig.decls.size) = assign1 x := by
  unfold cnfSatAssignment mixAssigns
  rw [dif_neg]
  · simp
  · omega

@[simp]
theorem satAssignment_inr (h : x < aig.decls.size) :
    (cnfSatAssignment aig assign1) x = ⟦aig, ⟨x, false, h⟩, assign1⟧ := by
  simp [cnfSatAssignment, mixAssigns, h]

inductive BiMark where
| bottom
| uninverted
| inverted
| top

namespace BiMark

@[inline]
def has (inversion : Bool) : BiMark → Bool
| bottom => false
| uninverted => !inversion
| inverted => inversion
| top => true

@[simp]
theorem has_bottom :
    has inversion bottom = false := by
  simp [has]

@[simp]
theorem has_uninverted :
    has inversion uninverted = !inversion := by
  simp [has]

@[simp]
theorem has_inverted :
    has inversion inverted = inversion := by
  simp [has]

@[simp]
theorem has_top :
    has inversion top = true := by
  simp [has]

theorem ext_iff {a b : BiMark} :
    a = b ↔ (a.has false = b.has false) ∧ (a.has true = b.has true) := by
  cases a <;> cases b <;> simp

instance instLE : LE BiMark where
  le a b := (a.has false ≤ b.has false) ∧ (a.has true ≤ b.has true)

theorem le_iff {a b : BiMark} :
    a ≤ b ↔ (a.has false ≤ b.has false) ∧ (a.has true ≤ b.has true) := by
  rfl

@[inline]
instance : DecidableLE BiMark := by
  simp +instances only [instLE, DecidableLE]
  infer_instance

@[simp]
theorem le_rfl {a : BiMark} :
    a ≤ a := by
  simp +instances only [instLE]
  simp [has]

theorem le_trans {a b c : BiMark} :
    a ≤ b → b ≤ c → a ≤ c := by
  simp +instances only [instLE, has]
  cases a <;> cases b <;> cases c
  <;> simp

@[simp]
theorem le_top :
    a ≤ top := by
  simp [le_iff]

@[simp]
theorem top_le :
    top ≤ a ↔ a = top := by
  constructor
  · simp +instances only [instLE, has]
    cases a <;> simp [show ¬(true ≤ false) by decide] <;> trivial
  · intro h
    simp [h]

@[simp]
theorem bottom_le :
    bottom ≤ a := by
  simp [le_iff]

theorem has_of_le {a b : BiMark} {inv : Bool} :
    a ≤ b → a.has inv → b.has inv := by
  simp only [le_iff, and_imp]
  cases inv
  <;> generalize has false a = hfa
  <;> generalize has true a = hfa
  <;> generalize has false b = hfb
  <;> generalize has true b = htb
  <;> decide +revert

@[inline]
def of (invert : Bool) : BiMark :=
  if invert then .inverted else uninverted

@[simp]
theorem has_of :
    has inversion (of invert) = (inversion = invert) := by
  simp [of]
  split <;> simp_all

@[inline]
def join : BiMark → BiMark → BiMark
| bottom, other
| other, bottom => other
| uninverted, uninverted => uninverted
| inverted, inverted => inverted
| _, _ => top

@[simp]
theorem has_join :
    (join a b).has inversion = (a.has inversion || b.has inversion) := by
  simp only [has, join]
  cases a
  <;> cases b
  <;> simp

@[simp]
theorem le_join_left :
    a ≤ (join a b) := by
  simp only [le_iff, has_join]
  cases has false a
  <;> cases has true a
  <;> simp

@[simp]
theorem le_join_right :
    b ≤ (join a b) := by
  simp only [le_iff, has_join]
  cases has false b
  <;> cases has true b
  <;> simp

@[simp]
theorem join_le (ha : a ≤ o) (hb : b ≤ o) :
    (join a b) ≤ o := by
  revert ha hb
  simp only [le_iff, has_join]
  generalize has false a = hfa
  generalize has false b = hfb
  generalize has false o = hfo
  generalize has true a = hta
  generalize has true b = htb
  generalize has true o = hto
  decide +revert

@[inline]
def meet : BiMark → BiMark → BiMark
| top, other
| other, top => other
| uninverted, uninverted => uninverted
| inverted, inverted => inverted
| _, _ => bottom

@[simp]
theorem has_meet :
    (meet a b).has inversion = (a.has inversion && b.has inversion) := by
  simp only [has, meet]
  cases a
  <;> cases b
  <;> simp

@[simp]
theorem meet_le_left :
    (meet a b) ≤ a := by
  simp only [le_iff, has_meet]
  cases has false a
  <;> cases has true a
  <;> simp

@[simp]
theorem meet_le_right :
    (meet a b) ≤ b := by
  simp only [le_iff, has_meet]
  cases has false a
  <;> cases has true a
  <;> simp

@[inline]
def invert : BiMark → Bool → BiMark
| uninverted, true => inverted
| inverted, true => uninverted
| a, _ => a

@[simp]
theorem has_invert :
    (invert a inv).has inversion = a.has (inversion ^^ inv) := by
  simp only [has, invert]
  cases a
  <;> cases inv
  <;> simp

@[inline]
def sub : BiMark → BiMark → BiMark
| a, bottom => a
| _, top
| bottom, _
| uninverted, uninverted
| inverted, inverted => bottom
| _, uninverted => inverted
| _, inverted => uninverted

@[simp]
theorem has_sub :
    (sub a b).has inversion = (a.has inversion && !b.has inversion) := by
  simp only [has, sub]
  cases a
  <;> cases b
  <;> simp

@[simp]
theorem join_sub :
    join (sub a b) b = join a b := by
  simp [ext_iff]
  generalize has false a = hfa
  generalize has false b = hfb
  generalize has true a = hta
  generalize has true b = htb
  decide +revert

end BiMark

/--
The central invariant for the `Cache`.

Relate satisfiability results about our produced CNF to satisfiability results about the AIG that
we are processing. The intuition for this is: if a node is marked, its CNF is already part of the
current CNF. Thus the current CNF is already mirroring the semantics of the marked node.
This means that if the CNF is satisfiable at some assignment, we can evaluate the marked node under
the atom part of that assignment and will get the value that was assigned to the corresponding
auxiliary variable as a result.
-/
def Cache.Inv (aig : AIG Nat) (cnf : CNF Nat) (marks : Array BiMark)
    (hmarks : marks.size = aig.decls.size) : Prop :=
  ∀ (assign : Nat → Bool) (_heval : cnf.eval assign = true) (idx : Nat) (inverted : Bool)
    (hbound : idx < aig.decls.size) (_hmark : marks[idx]'(by omega) |>.has inverted),
      (((projectRightAssign assign) idx) ^^ inverted)
        ≤
      ⟦aig, ⟨idx, inverted, hbound⟩, projectLeftAssign aig assign⟧

/--
The `Cache` invariant always holds for an empty CNF when all nodes are unmarked.
-/
theorem Cache.Inv_init : Inv aig .empty (.replicate aig.decls.size .bottom)
    (by simp) := by
  intro assign _ idx inverted hbound hmark
  simp at hmark

/--
The CNF cache. It keeps track of AIG nodes that we already turned into CNF to avoid adding the same
CNF twice.
-/
structure Cache (aig : AIG Nat) (cnf : CNF Nat) where
  /--
  Keeps track of AIG nodes that we already turned into CNF.
  -/
  marks : Array BiMark
  /--
  There are always as many marks as AIG nodes.
  -/
  hmarks : marks.size = aig.decls.size
  /--
  The invariant to make sure that `marks` is well formed with respect to the `cnf`
  -/
  inv : Cache.Inv aig cnf marks hmarks

/--
We say that a cache extends another by an index when it doesn't invalidate any entry and has an
entry for that index.
-/
structure Cache.IsExtensionBy (cache1 : Cache aig cnf1) (cache2 : Cache aig cnf2) (new : Nat) (mark : BiMark)
    (hnew : new < aig.decls.size) : Prop where
  /--
  No entry is invalidated.
  -/
  extension : ∀ (idx : Nat) (hidx : idx < aig.decls.size),
                cache1.marks[idx]'(by have := cache1.hmarks; omega) ≤
                cache2.marks[idx]'(by have := cache2.hmarks; omega)
  /--
  The second cache is true at the new index.
  -/
  trueAt : mark ≤ cache2.marks[new]'(by have := cache2.hmarks; omega)

theorem Cache.IsExtensionBy_trans_left (cache1 : Cache aig cnf1) (cache2 : Cache aig cnf2)
    (cache3 : Cache aig cnf3) (h12 : IsExtensionBy cache1 cache2 new1 mark1 hnew1)
    (h23 : IsExtensionBy cache2 cache3 new2 mark2 hnew2) : IsExtensionBy cache1 cache3 new1 mark1 hnew1 := by
  apply IsExtensionBy.mk
  · intro idx hidx
    exact BiMark.le_trans (h12.extension idx hidx) (h23.extension idx hidx)
  · exact BiMark.le_trans (h12.trueAt) (h23.extension new1 hnew1)

theorem Cache.IsExtensionBy_trans_right (cache1 : Cache aig cnf1) (cache2 : Cache aig cnf2)
    (cache3 : Cache aig cnf3) (h12 : IsExtensionBy cache1 cache2 new1 mark1 hnew1)
    (h23 : IsExtensionBy cache2 cache3 new2 mark2 hnew2) : IsExtensionBy cache1 cache3 new2 mark2 hnew2 := by
  apply IsExtensionBy.mk
  · intro idx hidx
    exact BiMark.le_trans (h12.extension idx hidx) (h23.extension idx hidx)
  · exact h23.trueAt

/--
Cache extension is a reflexive relation.
-/
theorem Cache.IsExtensionBy_rfl (cache : Cache aig cnf) {h}
    (hmarked : mark ≤ cache.marks[idx]'h) :
    Cache.IsExtensionBy cache cache idx mark (have := cache.hmarks; omega) := by
  apply IsExtensionBy.mk
  · simp
  · exact hmarked

theorem Cache.IsExtensionBy_le (cache1 : Cache aig cnf1) (cache2 : Cache aig cnf2) {h}
    (h12 : Cache.IsExtensionBy cache1 cache2 idx mark1 h) (hle : mark2 ≤ mark1) :
    Cache.IsExtensionBy cache1 cache2 idx mark2 hnew := by
  apply IsExtensionBy.mk
  · exact h12.extension
  · exact BiMark.le_trans hle h12.trueAt

theorem Cache.IsExtensionBy_join {cache1 : Cache aig cnf1} {cache2 : Cache aig cnf2} {h}
    (h1 : Cache.IsExtensionBy cache1 cache2 idx mark1 h)
    (h2 : Cache.IsExtensionBy cache1 cache2 idx mark2 h)
    (hjoin : mark3 ≤ mark1.join mark2) :
    Cache.IsExtensionBy cache1 cache2 idx mark3 hnew := by
  apply IsExtensionBy.mk
  · exact h1.extension
  · apply BiMark.le_trans hjoin
    exact BiMark.join_le h1.trueAt h2.trueAt

theorem Cache.IsExtensionBy_set (cache1 : Cache aig cnf1) (cache2 : Cache aig cnf2) (idx : Nat)
    (mark : BiMark) (hbound : idx < cache1.marks.size)
    (h : cache2.marks = cache1.marks.set idx mark)
    (hle : cache1.marks[idx]'hbound ≤ mark) :
    IsExtensionBy cache1 cache2 idx mark (by have := cache1.hmarks; omega) := by
  apply IsExtensionBy.mk
  · intro idx hidx
    simp only [Array.getElem_set, h]
    split <;> simp_all
  · simp [h]

theorem Cache.IsExtensionBy_modify (cache1 : Cache aig cnf1) (cache2 : Cache aig cnf2) (idx : Nat)
    (mark : BiMark) (hbound : idx < cache1.marks.size)
    (h : cache2.marks = cache1.marks.modify idx (·.join mark)) :
    IsExtensionBy cache1 cache2 idx mark (by have := cache1.hmarks; omega) := by
  apply IsExtensionBy.mk
  · intro idx hidx
    simp only [Array.getElem_modify, h]
    split <;> simp
  · simp [h, Array.getElem_modify]

/--
A cache with no entries is valid for an empty CNF.
-/
def Cache.init (aig : AIG Nat) : Cache aig .empty where
  marks := .replicate aig.decls.size .bottom
  hmarks := by simp
  inv := Inv_init

/--
Add a `Decl.false` to a `Cache`.
-/
def Cache.addFalse (cache : Cache aig cnf) (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .false) :
    {
      out : Cache aig (cnf ++ Decl.falseToCNF idx)
        //
      Cache.IsExtensionBy cache out idx .top h
    } :=
  have hmarkbound : idx < cache.marks.size := by have := cache.hmarks; omega
  let out :=
    { cache with
      marks := cache.marks.set idx .top
      hmarks := by simp [cache.hmarks]
      inv := by
        intro assign heval idx inverted hbound hmarked
        rw [Array.getElem_set] at hmarked
        split at hmarked
        next heq =>
          simp [heq] at htip heval
          simp [denote_idx_false htip, heval]
        next heq =>
          simp only [CNF.eval_append, Decl.falseToCNF_eval, Bool.and_eq_true, beq_iff_eq] at heval
          have := cache.inv assign heval.left idx inverted hbound hmarked
          apply this
    }
  ⟨out, IsExtensionBy_set cache out idx .top hmarkbound (by simp [out]) (by simp)⟩

/--
Add a `Decl.atom` to a cache.
-/
def Cache.addAtom (cache : Cache aig cnf) (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .atom a) :
    {
      out : Cache aig ((cnf ++ Decl.atomToCNF idx (a + aig.decls.size)))
        //
      Cache.IsExtensionBy cache out idx .top h
    } :=
  have hmarkbound : idx < cache.marks.size := by have := cache.hmarks; omega
  let out :=
    { cache with
      marks := cache.marks.set idx .top
      hmarks := by simp [cache.hmarks]
      inv := by
        intro assign heval idx inverted hbound hmarked
        rw [Array.getElem_set] at hmarked
        split at hmarked
        next heq =>
          simp only [heq, CNF.eval_append, Decl.atomToCNF_eval, Bool.and_eq_true, beq_iff_eq] at htip heval
          simp [heval, denote_idx_atom htip]
        next heq =>
          simp only [CNF.eval_append, Decl.atomToCNF_eval, Bool.and_eq_true, beq_iff_eq] at heval
          have := cache.inv assign heval.left idx inverted hbound hmarked
          apply this
    }
  ⟨out, IsExtensionBy_set cache out idx .top hmarkbound (by simp [out]) (by simp)⟩

def Cache.addGatePos (cache : Cache aig cnf) {hlb} {hrb} (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .gate lhs rhs) (hl : cache.marks[lhs.gate]'hlb |>.has lhs.invert)
    (hr : cache.marks[rhs.gate]'hrb |>.has rhs.invert) :
    {
      out : Cache aig (cnf ++ Decl.gatePosToCNF idx lhs.gate rhs.gate lhs.invert rhs.invert)
        //
      Cache.IsExtensionBy cache out idx .uninverted h
    } :=
  have := aig.hdag h htip
  have hmarkbound : idx < cache.marks.size := by have := cache.hmarks; omega
  let out :=
    { cache with
      marks := cache.marks.modify idx (·.join .uninverted)
      hmarks := by simp [cache.hmarks]
      inv := by
        intro assign heval idx inverted hbound hmarked
        rw [Array.getElem_modify] at hmarked
        split at hmarked
        next heq =>
          simp only [heq, CNF.eval_append, Decl.gatePosToCNF_eval, ge_iff_le, Bool.and_eq_true,
            decide_eq_true_eq] at htip heval
          cases inverted
          · have hleval := cache.inv assign heval.left lhs.gate lhs.invert (by omega) hl
            have hreval := cache.inv assign heval.left rhs.gate rhs.invert (by omega) hr
            simp [denote_idx_gate htip]
            replace heval := heval.right
            revert heval hleval hreval
            simp only [show ∀ (f : Fanin) h assign, ⟦aig, ⟨f.gate, f.invert, h⟩, assign⟧ = (⟦aig, ⟨f.gate, false, h⟩, assign⟧ ^^ f.invert) by
              intro f; cases f.invert <;> simp, projectRightAssign_property]
            generalize lhs.invert = linv
            generalize rhs.invert = rinv
            generalize ⟦aig, ⟨lhs.gate, false, by omega⟩, projectLeftAssign aig assign⟧ = lval
            generalize ⟦aig, ⟨rhs.gate, false, by omega⟩, projectLeftAssign aig assign⟧ = rval
            generalize assign lhs.gate = lgate
            generalize assign rhs.gate = rgate
            generalize assign idx = out
            decide +revert
          · simp at hmarked
            apply cache.inv assign heval.left idx true hbound hmarked
        next heq =>
          simp only [CNF.eval_append, Bool.and_eq_true] at heval
          apply cache.inv assign heval.left idx inverted hbound hmarked
    }
  ⟨out, IsExtensionBy_modify cache out idx .uninverted hmarkbound (by simp [out])⟩

def Cache.addGateNeg (cache : Cache aig cnf) {hlb} {hrb} (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .gate lhs rhs) (hl : cache.marks[lhs.gate]'hlb |>.has !lhs.invert)
    (hr : cache.marks[rhs.gate]'hrb |>.has !rhs.invert) :
    {
      out : Cache aig (cnf ++ Decl.gateNegToCNF idx lhs.gate rhs.gate lhs.invert rhs.invert)
        //
      Cache.IsExtensionBy cache out idx .inverted h
    } :=
  have := aig.hdag h htip
  have hmarkbound : idx < cache.marks.size := by have := cache.hmarks; omega
  let out :=
    { cache with
      marks := cache.marks.modify idx (·.join .inverted)
      hmarks := by simp [cache.hmarks]
      inv := by
        intro assign heval idx inverted hbound hmarked
        rw [Array.getElem_modify] at hmarked
        split at hmarked
        next heq =>
          simp only [heq, CNF.eval_append, Decl.gateNegToCNF_eval, Bool.and_eq_true,
            decide_eq_true_eq] at htip heval
          cases inverted
          · simp at hmarked
            apply cache.inv assign heval.left idx false hbound hmarked
          · have hleval := cache.inv assign heval.left lhs.gate (!lhs.invert) (by omega) hl
            have hreval := cache.inv assign heval.left rhs.gate (!rhs.invert) (by omega) hr
            simp [denote_idx_gate htip]
            replace heval := heval.right
            revert heval hleval hreval
            simp only [show ∀ g inv h assign, ⟦aig, ⟨g, !inv, h⟩, assign⟧ = !⟦aig, ⟨g, inv, h⟩, assign⟧ by
              intro f inv; cases inv <;> simp, projectRightAssign_property]
            simp only [show ∀ (f : Fanin) h assign, ⟦aig, ⟨f.gate, f.invert, h⟩, assign⟧ = (⟦aig, ⟨f.gate, false, h⟩, assign⟧ ^^ f.invert) by
              intro f; cases f.invert <;> simp]
            generalize lhs.invert = linv
            generalize rhs.invert = rinv
            generalize ⟦aig, ⟨lhs.gate, false, by omega⟩, projectLeftAssign aig assign⟧ = lval
            generalize ⟦aig, ⟨rhs.gate, false, by omega⟩, projectLeftAssign aig assign⟧ = rval
            generalize assign lhs.gate = lgate
            generalize assign rhs.gate = rgate
            generalize assign idx = out
            decide +revert
        next heq =>
          simp only [CNF.eval_append, Bool.and_eq_true] at heval
          apply cache.inv assign heval.left idx inverted hbound hmarked
    }
  ⟨out, IsExtensionBy_modify cache out idx .inverted hmarkbound (by simp [out])⟩

def Cache.addItePos (cache : Cache aig cnf) {cond ifTrue ifFalse : Fanin} (idx : Nat) {hcb htb hfb}
    (h : idx < aig.decls.size)
    (hltc : cond.gate < idx) (hltt : ifTrue.gate < idx) (hltf : ifFalse.gate < idx)
    (hc : cache.marks[cond.gate]'hcb = .top)
    (ht : cache.marks[ifTrue.gate]'htb |>.has ifTrue.invert)
    (hf : cache.marks[ifFalse.gate]'hfb |>.has ifFalse.invert)
    (hdenote : ∀ assign, ⟦aig, ⟨idx, false, h⟩, assign⟧ =
      ite
        ⟦aig, ⟨cond.gate, cond.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifTrue.gate, ifTrue.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifFalse.gate, ifFalse.invert, by omega⟩, assign⟧) :
    {
      out : Cache aig (cnf ++ Decl.itePosToCNF idx cond.gate ifTrue.gate ifFalse.gate cond.invert ifTrue.invert ifFalse.invert)
        //
      Cache.IsExtensionBy cache out idx .uninverted h
    } :=
  have hmarkbound : idx < cache.marks.size := by have := cache.hmarks; omega
  let out :=
    { cache with
      marks := cache.marks.modify idx (·.join .uninverted)
      hmarks := by simp [cache.hmarks]
      inv := by
        intro assign heval idx inverted hbound hmarked
        rw [Array.getElem_modify] at hmarked
        split at hmarked
        next heq =>
          simp only [CNF.eval_append, Decl.itePosToCNF_eval, ge_iff_le, Bool.and_eq_true,
            decide_eq_true_eq] at heval
          cases inverted
          · have hcpeval := cache.inv assign heval.left cond.gate cond.invert (by omega) (by simp [hc])
            have hcneval := cache.inv assign heval.left cond.gate (!cond.invert) (by omega) (by simp [hc])
            have hteval := cache.inv assign heval.left ifTrue.gate ifTrue.invert (by omega) ht
            have hfeval := cache.inv assign heval.left ifFalse.gate ifFalse.invert (by omega) hf
            replace heval := heval.right
            subst heq
            simp only [hdenote]
            revert heval hcpeval hcneval hteval hfeval
            simp only [show ∀ g inv h assign, ⟦aig, ⟨g, !inv, h⟩, assign⟧ = !⟦aig, ⟨g, inv, h⟩, assign⟧ by
              intro f inv; cases inv <;> simp, projectRightAssign_property]
            simp only [show ∀ (f : Fanin) h assign, ⟦aig, ⟨f.gate, f.invert, h⟩, assign⟧ = (⟦aig, ⟨f.gate, false, h⟩, assign⟧ ^^ f.invert) by
              intro f; cases f.invert <;> simp]
            generalize cond.invert = cinv
            generalize ifTrue.invert = tinv
            generalize ifFalse.invert = finv
            generalize ⟦aig, ⟨cond.gate, false, by omega⟩, projectLeftAssign aig assign⟧ = cval
            generalize ⟦aig, ⟨ifTrue.gate, false, by omega⟩, projectLeftAssign aig assign⟧ = tval
            generalize ⟦aig, ⟨ifFalse.gate, false, by omega⟩, projectLeftAssign aig assign⟧ = fval
            generalize assign cond.gate = cgate
            generalize assign ifTrue.gate = tgate
            generalize assign ifFalse.gate = fgate
            generalize assign idx = out
            decide +revert
          · simp at hmarked
            apply cache.inv assign heval.left idx true hbound hmarked
        next heq =>
          simp only [CNF.eval_append, Bool.and_eq_true] at heval
          apply cache.inv assign heval.left idx inverted hbound hmarked
    }
  ⟨out, IsExtensionBy_modify cache out idx .uninverted hmarkbound (by simp [out])⟩

def Cache.addIteNeg (cache : Cache aig cnf) {cond ifTrue ifFalse : Fanin} (idx : Nat) {hcb htb hfb}
    (h : idx < aig.decls.size)
    (hltc : cond.gate < idx) (hltt : ifTrue.gate < idx) (hltf : ifFalse.gate < idx)
    (hc : cache.marks[cond.gate]'hcb = .top)
    (ht : cache.marks[ifTrue.gate]'htb |>.has !ifTrue.invert)
    (hf : cache.marks[ifFalse.gate]'hfb |>.has !ifFalse.invert)
    (hdenote : ∀ assign, ⟦aig, ⟨idx, false, h⟩, assign⟧ =
      ite
        ⟦aig, ⟨cond.gate, cond.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifTrue.gate, ifTrue.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifFalse.gate, ifFalse.invert, by omega⟩, assign⟧) :
    {
      out : Cache aig (cnf ++ Decl.iteNegToCNF idx cond.gate ifTrue.gate ifFalse.gate cond.invert ifTrue.invert ifFalse.invert)
        //
      Cache.IsExtensionBy cache out idx .inverted h
    } :=
  have hmarkbound : idx < cache.marks.size := by have := cache.hmarks; omega
  let out :=
    { cache with
      marks := cache.marks.modify idx (·.join .inverted)
      hmarks := by simp [cache.hmarks]
      inv := by
        intro assign heval idx inverted hbound hmarked
        rw [Array.getElem_modify] at hmarked
        split at hmarked
        next heq =>
          simp only [CNF.eval_append, Decl.iteNegToCNF_eval, Bool.and_eq_true,
            decide_eq_true_eq] at heval
          cases inverted
          · simp at hmarked
            apply cache.inv assign heval.left idx false hbound hmarked
          · have hcpeval := cache.inv assign heval.left cond.gate cond.invert (by omega) (by simp [hc])
            have hcneval := cache.inv assign heval.left cond.gate (!cond.invert) (by omega) (by simp [hc])
            have hteval := cache.inv assign heval.left ifTrue.gate (!ifTrue.invert) (by omega) ht
            have hfeval := cache.inv assign heval.left ifFalse.gate (!ifFalse.invert) (by omega) hf
            replace heval := heval.right
            subst heq
            rw [show ∀ g inv h assign, ⟦aig, ⟨g, inv, h⟩, assign⟧ = (⟦aig, ⟨g, false, h⟩, assign⟧ ^^ inv) by
              intro f inv; cases inv <;> simp, projectRightAssign_property]
            simp only [hdenote]
            revert heval hcpeval hcneval hteval hfeval
            simp only [show ∀ g inv h assign, ⟦aig, ⟨g, !inv, h⟩, assign⟧ = !⟦aig, ⟨g, inv, h⟩, assign⟧ by
              intro f inv; cases inv <;> simp, projectRightAssign_property]
            simp only [show ∀ (f : Fanin) h assign, ⟦aig, ⟨f.gate, f.invert, h⟩, assign⟧ = (⟦aig, ⟨f.gate, false, h⟩, assign⟧ ^^ f.invert) by
              intro f; cases f.invert <;> simp]
            generalize cond.invert = cinv
            generalize ifTrue.invert = tinv
            generalize ifFalse.invert = finv
            generalize ⟦aig, ⟨cond.gate, false, by omega⟩, projectLeftAssign aig assign⟧ = cval
            generalize ⟦aig, ⟨ifTrue.gate, false, by omega⟩, projectLeftAssign aig assign⟧ = tval
            generalize ⟦aig, ⟨ifFalse.gate, false, by omega⟩, projectLeftAssign aig assign⟧ = fval
            generalize assign cond.gate = cgate
            generalize assign ifTrue.gate = tgate
            generalize assign ifFalse.gate = fgate
            generalize assign idx = out
            decide +revert
        next heq =>
          simp only [CNF.eval_append, Bool.and_eq_true] at heval
          apply cache.inv assign heval.left idx inverted hbound hmarked
    }
  ⟨out, IsExtensionBy_modify cache out idx .inverted hmarkbound (by simp [out])⟩

/--
The key invariant about the `State` itself (without cache): The CNF we produce is always satisfiable
at `cnfSatAssignment`.
-/
def State.Inv (aig : AIG Nat) (cnf : CNF Nat) : Prop :=
  ∀ (assign1 : Nat → Bool), cnf.Sat (cnfSatAssignment aig assign1)

/--
The `State` invariant always holds when we have an empty CNF.
-/
theorem State.Inv_nil : State.Inv aig (.empty : CNF Nat) := by
  simp [State.Inv]

/--
Combining two CNFs for which `State.Inv` holds preserves `State.Inv`.
-/
theorem State.Inv_append (h1 : State.Inv aig cnf1) (h2 : State.Inv aig cnf2) :
    State.Inv aig (cnf1 ++ cnf2) := by
  intro assign1
  specialize h1 assign1
  specialize h2 assign1
  simp [CNF.sat_def] at h1 h2 ⊢
  constructor <;> assumption

/--
`State.Inv` holds for the CNF that we produce for a `Decl.false`.
-/
theorem State.Inv_falseToCNF {upper : Nat} {h : upper < aig.decls.size}
    (heq : aig.decls[upper] = .false) :
    State.Inv aig (Decl.falseToCNF upper) := by
  intro assign1
  simp [CNF.sat_def, denote_idx_false heq, h]

/--
`State.Inv` holds for the CNF that we produce for a `Decl.atom`
-/
theorem State.Inv_atomToCNF {h : upper < aig.decls.size}
    (heq : aig.decls[upper] = .atom a) :
    State.Inv aig (Decl.atomToCNF upper (a + aig.decls.size)) := by
  intro assign1
  simp [CNF.sat_def, denote_idx_atom heq, h]

theorem State.Inv_gatePosToCNF {aig : AIG Nat} {h}
    (heq : aig.decls[upper]'h = .gate lhs rhs) :
    State.Inv aig (Decl.gatePosToCNF upper lhs.gate rhs.gate lhs.invert rhs.invert) := by
  intro assign1
  have hlhs : lhs.gate < aig.decls.size := Nat.lt_trans (aig.hdag h heq).left h
  have hrhs : rhs.gate < aig.decls.size := Nat.lt_trans (aig.hdag h heq).right h
  generalize hlinv : lhs.invert = linv
  generalize hrinv : rhs.invert = rinv
  rw [CNF.sat_def]
  cases linv <;> cases rinv <;> simp [denote_idx_gate heq, hlinv, hrinv, h, hlhs, hrhs]

theorem State.Inv_gateNegToCNF {aig : AIG Nat} {h}
    (heq : aig.decls[upper]'h = .gate lhs rhs) :
    State.Inv aig (Decl.gateNegToCNF upper lhs.gate rhs.gate lhs.invert rhs.invert) := by
  intro assign1
  have hlhs : lhs.gate < aig.decls.size := Nat.lt_trans (aig.hdag h heq).left h
  have hrhs : rhs.gate < aig.decls.size := Nat.lt_trans (aig.hdag h heq).right h
  generalize hlinv : lhs.invert = linv
  generalize hrinv : rhs.invert = rinv
  rw [CNF.sat_def]
  cases linv <;> cases rinv <;> simp [denote_idx_gate heq, hlinv, hrinv, h, hlhs, hrhs]

theorem State.Inv_itePosToCNF {aig : AIG Nat} {cond ifTrue ifFalse : Fanin} {idx : Nat}
    (h : idx < aig.decls.size)
    (hltc : cond.gate < idx) (hltt : ifTrue.gate < idx) (hltf : ifFalse.gate < idx)
    (hdenote : ∀ assign, ⟦aig, ⟨idx, false, h⟩, assign⟧ =
      ite
        ⟦aig, ⟨cond.gate, cond.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifTrue.gate, ifTrue.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifFalse.gate, ifFalse.invert, by omega⟩, assign⟧) :
    State.Inv aig (Decl.itePosToCNF idx cond.gate ifTrue.gate ifFalse.gate cond.invert ifTrue.invert ifFalse.invert) := by
  intro assign1
  rw [CNF.sat_def, Decl.itePosToCNF_eval, satAssignment_inr h, hdenote, satAssignment_inr (by omega),
    satAssignment_inr (by omega), satAssignment_inr (by omega)]
  have {fi : Fanin} {aig h} {assign : Nat → Bool} :
    ⟦aig, ⟨fi.gate, fi.invert, h⟩, assign⟧ = (⟦aig, ⟨fi.gate, false, h⟩, assign⟧ ^^ fi.invert) := by
      cases fi.invert <;> simp
  simp [this]

theorem State.Inv_iteNegToCNF {aig : AIG Nat} {cond ifTrue ifFalse : Fanin} {idx : Nat}
    (h : idx < aig.decls.size)
    (hltc : cond.gate < idx) (hltt : ifTrue.gate < idx) (hltf : ifFalse.gate < idx)
    (hdenote : ∀ assign, ⟦aig, ⟨idx, false, h⟩, assign⟧ =
      ite
        ⟦aig, ⟨cond.gate, cond.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifTrue.gate, ifTrue.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifFalse.gate, ifFalse.invert, by omega⟩, assign⟧) :
    State.Inv aig (Decl.iteNegToCNF idx cond.gate ifTrue.gate ifFalse.gate cond.invert ifTrue.invert ifFalse.invert) := by
  intro assign1
  rw [CNF.sat_def, Decl.iteNegToCNF_eval, satAssignment_inr h, hdenote, satAssignment_inr (by omega),
    satAssignment_inr (by omega), satAssignment_inr (by omega)]
  have {fi : Fanin} {aig h} {assign : Nat → Bool} :
    ⟦aig, ⟨fi.gate, fi.invert, h⟩, assign⟧ = (⟦aig, ⟨fi.gate, false, h⟩, assign⟧ ^^ fi.invert) := by
      cases fi.invert <;> simp
  simp [this]

/--
The state to accumulate CNF clauses as we run our Tseitin transformation on the AIG.
-/
structure State (aig : AIG Nat) where
  /--
  The CNF clauses so far.
  -/
  cnf : CNF Nat
  /--
  A cache so that we don't generate CNF for an AIG node more than once.
  -/
  cache : Cache aig cnf
  /--
  The invariant that `cnf` has to maintain as we build it up.
  -/
  inv : State.Inv aig cnf

/--
An initial state with no CNF clauses and an empty cache.
-/
def State.empty (aig : AIG Nat) : State aig where
  cnf := .emptyWithCapacity (aig.decls.size * 2)
  cache := Cache.init aig
  inv := State.Inv_nil

/--
State extension are `Cache.IsExtensionBy` for now.
-/
abbrev State.IsExtensionBy (state1 : State aig) (state2 : State aig) (new : Nat) (mark : BiMark)
    (hnew : new < aig.decls.size) : Prop :=
  Cache.IsExtensionBy state1.cache state2.cache new mark hnew

theorem State.IsExtensionBy_trans_left (state1 : State aig) (state2 : State aig)
    (state3 : State aig) (h12 : IsExtensionBy state1 state2 new1 mark1 hnew1)
    (h23 : IsExtensionBy state2 state3 new2 mark2 hnew2) : IsExtensionBy state1 state3 new1 mark1 hnew1 := by
  apply Cache.IsExtensionBy_trans_left
  · exact h12
  · exact h23

theorem State.IsExtensionBy_trans_right (state1 : State aig) (state2 : State aig)
    (state3 : State aig) (h12 : IsExtensionBy state1 state2 new1 mark1 hnew1)
    (h23 : IsExtensionBy state2 state3 new2 mark2 hnew2) : IsExtensionBy state1 state3 new2 mark2 hnew2 := by
  apply  Cache.IsExtensionBy_trans_right
  · exact h12
  · exact h23

/--
State extension is a reflexive relation.
-/
theorem State.IsExtensionBy_rfl (state : State aig) {h}
    (hmarked : mark ≤ state.cache.marks[idx]'h) :
    State.IsExtensionBy state state idx mark (have := state.cache.hmarks; omega) := by
  apply Cache.IsExtensionBy_rfl <;> assumption

theorem State.IsExtensionBy_le {state1 : State aig} {state2 : State aig} {h}
    (h12 : IsExtensionBy state1 state2 idx mark1 h) (hle : mark2 ≤ mark1) :
    IsExtensionBy state1 state2 idx mark2 hnew := by
  apply Cache.IsExtensionBy_le <;> assumption

theorem State.IsExtensionBy_join {state1 : State aig} {state2 : State aig} {h}
    (h1 : State.IsExtensionBy state1 state2 idx mark1 h)
    (h2 : State.IsExtensionBy state1 state2 idx mark2 h)
    (hjoin : mark3 ≤ mark1.join mark2) :
    State.IsExtensionBy state1 state2 idx mark3 hnew := by
  exact Cache.IsExtensionBy_join h1 h2 hjoin

/--
Add the CNF for a `Decl.false` to the state.
-/
def State.addFalse (state : State aig) (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .false) :
    { out : State aig // State.IsExtensionBy state out idx .top h } :=
  let ⟨cnf, cache, inv⟩ := state
  let newCnf := Decl.falseToCNF idx
  have hinv := toCNF.State.Inv_falseToCNF htip
  let ⟨cache, hcache⟩ := cache.addFalse idx h htip
  ⟨⟨cnf ++ newCnf, cache, State.Inv_append inv hinv⟩, by simp [newCnf, hcache]⟩

/--
Add the CNF for a `Decl.atom` to the state.
-/
def State.addAtom (state : State aig) (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .atom a) :
    { out : State aig // State.IsExtensionBy state out idx .top h } :=
  let ⟨cnf, cache, inv⟩ := state
  let newCnf := Decl.atomToCNF idx (a + aig.decls.size)
  have hinv := toCNF.State.Inv_atomToCNF htip
  let ⟨cache, hcache⟩ := cache.addAtom idx h htip
  ⟨⟨cnf ++ newCnf, cache, State.Inv_append inv hinv⟩, by simp [newCnf, hcache]⟩

def State.addGatePos (state : State aig) {hlb} {hrb} (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .gate lhs rhs) (hl : state.cache.marks[lhs.gate]'hlb |>.has lhs.invert)
    (hr : state.cache.marks[rhs.gate]'hrb |>.has rhs.invert ) :
    { out : State aig // State.IsExtensionBy state out idx .uninverted h } :=
  have := aig.hdag h htip
  let ⟨cnf, cache, inv⟩ := state
  let newCnf := Decl.gatePosToCNF idx lhs.gate rhs.gate lhs.invert rhs.invert
  have hinv := toCNF.State.Inv_gatePosToCNF htip
  let ⟨cache, hcache⟩ := cache.addGatePos idx h htip hl hr
  ⟨⟨cnf ++ newCnf, cache, State.Inv_append inv hinv⟩, by simp [newCnf, hcache]⟩

def State.addGateNeg (state : State aig) {hlb} {hrb} (idx : Nat) (h : idx < aig.decls.size)
    (htip : aig.decls[idx]'h = .gate lhs rhs) (hl : state.cache.marks[lhs.gate]'hlb |>.has !lhs.invert)
    (hr : state.cache.marks[rhs.gate]'hrb |>.has !rhs.invert ) :
    { out : State aig // State.IsExtensionBy state out idx .inverted h } :=
  have := aig.hdag h htip
  let ⟨cnf, cache, inv⟩ := state
  let newCnf := Decl.gateNegToCNF idx lhs.gate rhs.gate lhs.invert rhs.invert
  have hinv := toCNF.State.Inv_gateNegToCNF htip
  let ⟨cache, hcache⟩ := cache.addGateNeg idx h htip hl hr
  ⟨⟨cnf ++ newCnf, cache, State.Inv_append inv hinv⟩, by simp [newCnf, hcache]⟩

def State.addItePos (state : State aig) {cond ifTrue ifFalse : Fanin} (idx : Nat) {hcb htb hfb}
    (h : idx < aig.decls.size)
    (hltc : cond.gate < idx) (hltt : ifTrue.gate < idx) (hltf : ifFalse.gate < idx)
    (hc : state.cache.marks[cond.gate]'hcb = .top)
    (ht : state.cache.marks[ifTrue.gate]'htb |>.has ifTrue.invert)
    (hf : state.cache.marks[ifFalse.gate]'hfb |>.has ifFalse.invert)
    (hdenote : ∀ assign, ⟦aig, ⟨idx, false, h⟩, assign⟧ =
      ite
        ⟦aig, ⟨cond.gate, cond.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifTrue.gate, ifTrue.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifFalse.gate, ifFalse.invert, by omega⟩, assign⟧) :
    { out : State aig // State.IsExtensionBy state out idx .uninverted h } :=
  let ⟨cnf, cache, inv⟩ := state
  let newCnf := Decl.itePosToCNF idx cond.gate ifTrue.gate ifFalse.gate cond.invert ifTrue.invert ifFalse.invert
  have hinv := toCNF.State.Inv_itePosToCNF h hltc hltt hltf hdenote
  let ⟨cache, hcache⟩ := cache.addItePos idx h hltc hltt hltf hc ht hf hdenote
  ⟨⟨cnf ++ newCnf, cache, State.Inv_append inv hinv⟩, by simp [newCnf, hcache]⟩

def State.addIteNeg (state : State aig) {cond ifTrue ifFalse : Fanin} (idx : Nat) {hcb htb hfb}
    (h : idx < aig.decls.size)
    (hltc : cond.gate < idx) (hltt : ifTrue.gate < idx) (hltf : ifFalse.gate < idx)
    (hc : state.cache.marks[cond.gate]'hcb = .top)
    (ht : state.cache.marks[ifTrue.gate]'htb |>.has !ifTrue.invert)
    (hf : state.cache.marks[ifFalse.gate]'hfb |>.has !ifFalse.invert)
    (hdenote : ∀ assign, ⟦aig, ⟨idx, false, h⟩, assign⟧ =
      ite
        ⟦aig, ⟨cond.gate, cond.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifTrue.gate, ifTrue.invert, by omega⟩, assign⟧
        ⟦aig, ⟨ifFalse.gate, ifFalse.invert, by omega⟩, assign⟧) :
    { out : State aig // State.IsExtensionBy state out idx .inverted h } :=
  let ⟨cnf, cache, inv⟩ := state
  let newCnf := Decl.iteNegToCNF idx cond.gate ifTrue.gate ifFalse.gate cond.invert ifTrue.invert ifFalse.invert
  have hinv := toCNF.State.Inv_iteNegToCNF h hltc hltt hltf hdenote
  let ⟨cache, hcache⟩ := cache.addIteNeg idx h hltc hltt hltf hc ht hf hdenote
  ⟨⟨cnf ++ newCnf, cache, State.Inv_append inv hinv⟩, by simp [newCnf, hcache]⟩

/--
Evaluate the CNF contained within the state.
-/
def State.eval (assign : Nat → Bool) (state : State aig) : Bool :=
  state.cnf.eval assign

/--
The CNF within the state is sat.
-/
def State.Sat (assign : Nat → Bool) (state : State aig) : Prop :=
  state.cnf.Sat assign

/--
The CNF within the state is unsat.
-/
def State.Unsat (state : State aig) : Prop :=
  state.cnf.Unsat

@[simp]
theorem State.eval_eq : State.eval assign state = state.cnf.eval assign := by
  simp [State.eval]

@[simp]
theorem State.sat_iff : State.Sat assign state ↔ state.cnf.Sat assign := by rfl

@[simp]
theorem State.unsat_iff : State.Unsat state ↔ state.cnf.Unsat := by rfl

/--
Detect if-then-else and XOR/XNOR gates of the form `(c → t) ∧ (¬c → f) = ¬(c ∧ ¬t) ∧ ¬(¬c ∧ ¬f)`.
-/
def detectIte {aig : AIG Nat} (root : Nat) (h : root < aig.decls.size) : Option (Fanin × Fanin × Fanin) := do
  -- Match root = (l ∧ r)
  let (eq:=hroot) .gate l r := aig.decls[root]'h | none
  have := aig.hdag h hroot

  -- We expect the structure to be a conjunction of disjunctions
  if ¬l.invert ∨ ¬r.invert then
    none

  -- Match l = (l0 ∧ l1)
  let (eq:=hl) .gate l0 l1 := aig.decls[l.gate] | none
  have := aig.hdag (by omega) hl

  -- Match r = (r0 ∧ r1)
  let (eq:=hr) .gate r0 r1 := aig.decls[r.gate] | none
  have := aig.hdag (by omega) hr

  -- ¬(l0 ∧ l1) ∧ ¬(¬l0 ∧ r1) = (l0 → ¬l1) ∧ (¬l0 → ¬r1)
  if l0 = r0.flip true then
    some (l0, l1.flip true, r1.flip true)

  -- ¬(l0 ∧ l1) ∧ ¬(r0 ∧ ¬l0) = (l0 → ¬l1) ∧ (¬l0 → ¬r0)
  else if l0 = r1.flip true then
    some (l0, l1.flip true, r0.flip true)

  -- ¬(l0 ∧ l1) ∧ ¬(¬l1 ∧ r1) = (l1 → ¬l0) ∧ (¬l0 → ¬r1)
  else if l1 = r0.flip true then
    some (l1, l0.flip true, r1.flip true)

  -- ¬(l0 ∧ l1) ∧ ¬(r0 ∧ ¬l1) = (l1 → ¬l0) ∧ (¬l1 → ¬r0)
  else if l1 = r1.flip true then
    some (l1, l0.flip true, r0.flip true)

  else
    none

theorem detectIte_cond_lt {aig : AIG Nat} {root c t f} {h : root < aig.decls.size}
    (heq : detectIte root h = some ⟨c, t, f⟩) :
    c.gate < root := by
  simp only [detectIte] at heq
  split at heq; (all_goals try contradiction); next l r hroot =>
  split at heq; (all_goals try contradiction); next hinvert =>
  split at heq; (all_goals try contradiction); next l0 l1 hl =>
  split at heq; (all_goals try contradiction); next r0 r1 hr =>
  have := aig.hdag (by omega) hroot
  have := aig.hdag (by omega) hl
  (repeat' (split at heq))
  <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at heq
  <;> rw [←heq.left]
  <;> omega

theorem detectIte_ifTrue_lt {aig : AIG Nat} {root c t f} {h : root < aig.decls.size}
    (heq : detectIte root h = some ⟨c, t, f⟩) :
    t.gate < root := by
  simp only [detectIte] at heq
  split at heq; (all_goals try contradiction); next l r hroot =>
  split at heq; (all_goals try contradiction); next hinvert =>
  split at heq; (all_goals try contradiction); next l0 l1 hl =>
  split at heq; (all_goals try contradiction); next r0 r1 hr =>
  have := aig.hdag (by omega) hroot
  have := aig.hdag (by omega) hl
  (repeat' (split at heq))
  <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at heq
  <;> rw [←heq.right.left, Fanin.gate_flip]
  <;> omega

theorem detectIte_ifFalse_lt {aig : AIG Nat} {root c t f} {h : root < aig.decls.size}
    (heq : detectIte root h = some ⟨c, t, f⟩) :
    f.gate < root := by
  simp only [detectIte] at heq
  split at heq; (all_goals try contradiction); next l r hroot =>
  split at heq; (all_goals try contradiction); next hinvert =>
  split at heq; (all_goals try contradiction); next l0 l1 hl =>
  split at heq; (all_goals try contradiction); next r0 r1 hr =>
  have := aig.hdag (by omega) hroot
  have := aig.hdag (by omega) hr
  (repeat' (split at heq))
  <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at heq
  <;> rw [←heq.right.right, Fanin.gate_flip]
  <;> omega

theorem denote_detectIte {root h c t f} (heq : detectIte root h = some ⟨c, t, f⟩) :
    ⟦aig, ⟨root, false, h⟩, assign⟧ =
      ite
        ⟦aig, ⟨c.gate, c.invert, by have := detectIte_cond_lt heq; omega⟩, assign⟧
        ⟦aig, ⟨t.gate, t.invert, by have := detectIte_ifTrue_lt heq; omega⟩, assign⟧
        ⟦aig, ⟨f.gate, f.invert, by have := detectIte_ifFalse_lt heq; omega⟩, assign⟧ := by
  simp only [detectIte] at heq
  split at heq; (all_goals try contradiction); next l r hroot =>
  split at heq; (all_goals try contradiction); next hinvert =>
  split at heq; (all_goals try contradiction); next l0 l1 hl =>
  split at heq; (all_goals try contradiction); next r0 r1 hr =>
  have := aig.hdag (by omega) hroot
  have := aig.hdag (by omega) hl
  have := aig.hdag (by omega) hr
  simp only [Bool.not_eq_true, not_or, Bool.not_eq_false] at hinvert
  rw [denote_idx_gate hroot, hinvert.left, hinvert.right, denote_idx_gate hl, denote_idx_gate hr]
  (repeat' (split at heq))
  <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at heq
  <;> rename_i h
  <;> simp only [h, Fanin.gate_flip, Fanin.invert_flip, Bool.bne_true, denote_not_invert,
    ← heq.left, ← heq.right.left, ← heq.right.right]
  <;> generalize ⟦aig, ⟨l0.gate, l0.invert, by omega⟩, assign⟧ = l0
  <;> generalize ⟦aig, ⟨l1.gate, l1.invert, by omega⟩, assign⟧ = l1
  <;> generalize ⟦aig, ⟨r0.gate, r0.invert, by omega⟩, assign⟧ = r0
  <;> generalize ⟦aig, ⟨r1.gate, r1.invert, by omega⟩, assign⟧ = r1
  <;> decide +revert

end toCNF

/--
Convert an AIG into CNF, starting at some entry node.
-/
public def toCNF (entry : Entrypoint Nat) : CNF Nat :=
  let ⟨state, _⟩ := go entry.aig entry.ref.gate (.of entry.ref.invert) entry.ref.hgate (toCNF.State.empty entry.aig)
  state.cnf.add [(entry.ref.gate, !entry.ref.invert)]
where
  go (aig : AIG Nat) (upper : Nat) (mark : toCNF.BiMark) (h : upper < aig.decls.size) (state : toCNF.State aig) :
      { out : toCNF.State aig // toCNF.State.IsExtensionBy state out upper mark h } :=
    let existingMark := state.cache.marks[upper]'(by have := state.cache.hmarks; omega)
    if hmarked : mark ≤ existingMark then
      ⟨state, by apply toCNF.State.IsExtensionBy_rfl <;> assumption⟩
    else
      let decl := aig.decls[upper]
      match heq : decl with
      | .false =>
        let res := state.addFalse upper h heq
        ⟨res.val, toCNF.State.IsExtensionBy_le res.property (by simp)⟩
      | .atom _ =>
        let res := state.addAtom upper h heq
        ⟨res.val, toCNF.State.IsExtensionBy_le res.property (by simp)⟩
      | .gate lhs rhs =>
        -- Only add the marks not present in the existing mark
        let fullMark := mark
        let mark := mark.sub existingMark
        have hmarkmeet {other} :
            state.IsExtensionBy other upper mark (by omega) →
            state.IsExtensionBy other upper fullMark (by omega) := by
          intro h
          have : state.IsExtensionBy other upper existingMark (by omega) := by
            apply toCNF.State.IsExtensionBy_trans_left (h23 := h)
            subst existingMark
            apply toCNF.State.IsExtensionBy_rfl
            · assumption
            · simp
            · have := state.cache.hmarks; omega
          apply toCNF.Cache.IsExtensionBy_join h this
          simp [mark, fullMark]

        match hite : toCNF.detectIte upper h with
        | some ⟨cond, ifTrue, ifFalse⟩ =>
          have hltc := toCNF.detectIte_cond_lt hite
          have hltt := toCNF.detectIte_ifTrue_lt hite
          have hltf := toCNF.detectIte_ifFalse_lt hite

          let ⟨cstate, hcstate⟩ := go aig cond.gate .top (by omega) state
          let ⟨tstate, htstate⟩ := go aig ifTrue.gate (mark.invert ifTrue.invert) (by omega) cstate
          let ⟨fstate, hfstate⟩ := go aig ifFalse.gate (mark.invert ifFalse.invert) (by omega) tstate

          have hcstate' : state.IsExtensionBy fstate cond.gate .top (by omega) := by
            apply toCNF.State.IsExtensionBy_trans_left (h23 := hfstate)
            apply toCNF.State.IsExtensionBy_trans_left (h23 := htstate)
            · exact hcstate

          have htstate' : cstate.IsExtensionBy fstate ifTrue.gate (mark.invert ifTrue.invert) (by omega) := by
            apply toCNF.State.IsExtensionBy_trans_left (h23 := hfstate)
            · exact htstate

          let ⟨posstate, hposstate⟩ : { out // fstate.IsExtensionBy out upper (mark.meet .uninverted) h } :=
            if hmark : mark.has false then
              let res :=
                fstate.addItePos upper h hltc hltt hltf
                  (toCNF.BiMark.top_le.mp hcstate'.trueAt)
                  (by apply toCNF.BiMark.has_of_le htstate'.trueAt; simp [hmark])
                  (by apply toCNF.BiMark.has_of_le hfstate.trueAt; simp [hmark])
                  (by simp [toCNF.denote_detectIte hite])
              ⟨res.val, toCNF.State.IsExtensionBy_le res.property (by simp)⟩
            else
              ⟨fstate, by
                apply toCNF.State.IsExtensionBy_rfl
                · assumption
                · simp at hmark
                  simp [toCNF.BiMark.le_iff, hmark]
                · simpa [fstate.cache.hmarks]
              ⟩

          have hcstate'' : state.IsExtensionBy posstate cond.gate .top (by omega) := by
            apply toCNF.State.IsExtensionBy_trans_left (h23 := hposstate)
            · exact hcstate'

          have htstate'' : cstate.IsExtensionBy posstate ifTrue.gate (mark.invert ifTrue.invert) (by omega) := by
            apply toCNF.State.IsExtensionBy_trans_left (h23 := hposstate)
            · exact htstate'

          have hfstate'' : tstate.IsExtensionBy posstate ifFalse.gate (mark.invert ifFalse.invert) (by omega) := by
            apply toCNF.State.IsExtensionBy_trans_left (h23 := hposstate)
            · exact hfstate

          let ⟨negstate, hnegstate⟩ : { out // posstate.IsExtensionBy out upper (mark.meet .inverted) h } :=
            if hmark : mark.has true then
              let res :=
                posstate.addIteNeg upper h hltc hltt hltf
                  (toCNF.BiMark.top_le.mp hcstate''.trueAt)
                  (by apply toCNF.BiMark.has_of_le htstate''.trueAt; simp [hmark])
                  (by apply toCNF.BiMark.has_of_le hfstate''.trueAt; simp [hmark])
                  (by simp [toCNF.denote_detectIte hite])
              ⟨res.val, toCNF.State.IsExtensionBy_le res.property (by simp)⟩
            else
              ⟨posstate, by
                apply toCNF.State.IsExtensionBy_rfl
                · assumption
                · simp at hmark
                  simp [toCNF.BiMark.le_iff, hmark]
                · simpa [posstate.cache.hmarks]
              ⟩

          have hposstate' : fstate.IsExtensionBy negstate upper (mark.meet .uninverted) (by omega) := by
            apply toCNF.State.IsExtensionBy_trans_left (h23 := hnegstate)
            · exact hposstate

          have hmarkstate : fstate.IsExtensionBy negstate upper mark (by omega) := by
            rw [show mark = (mark.meet .uninverted).join (mark.meet .inverted) by simp [toCNF.BiMark.ext_iff]]
            apply toCNF.State.IsExtensionBy_join hposstate' ?_ (toCNF.BiMark.le_rfl)
            apply toCNF.State.IsExtensionBy_trans_right (h12 := hposstate) (h23 := hnegstate)

          ⟨negstate, hmarkmeet <| toCNF.State.IsExtensionBy_trans_right (h12 := hcstate') (h23 := hmarkstate)⟩
        | none =>
          have := aig.hdag h heq
          let ⟨lstate, hlstate⟩ := go aig lhs.gate (mark.invert lhs.invert) (by omega) state
          let ⟨rstate, hrstate⟩ := go aig rhs.gate (mark.invert rhs.invert) (by omega) lstate

          have hlstate' : state.IsExtensionBy rstate lhs.gate (mark.invert lhs.invert) (by omega) := by
            apply toCNF.State.IsExtensionBy_trans_left
            · exact hlstate
            · exact hrstate

          let ⟨posstate, hposstate⟩ : { out // rstate.IsExtensionBy out upper (mark.meet .uninverted) h } :=
            if hmark : mark.has false then
              let res :=
                rstate.addGatePos upper h heq
                  (by apply toCNF.BiMark.has_of_le hlstate'.trueAt; simp [hmark])
                  (by apply toCNF.BiMark.has_of_le hrstate.trueAt; simp [hmark])
              ⟨res.val, toCNF.State.IsExtensionBy_le res.property (by simp)⟩
            else
              ⟨rstate, by
                apply toCNF.State.IsExtensionBy_rfl
                · assumption
                · simp at hmark
                  simp [toCNF.BiMark.le_iff, hmark]
                · simpa [rstate.cache.hmarks]
              ⟩

          have hlstate'' : state.IsExtensionBy posstate lhs.gate (mark.invert lhs.invert) (by omega) := by
            apply toCNF.State.IsExtensionBy_trans_left (h23 := hposstate)
            · exact hlstate'

          have hrstate'' : lstate.IsExtensionBy posstate rhs.gate (mark.invert rhs.invert) (by omega) := by
            apply toCNF.State.IsExtensionBy_trans_left (h23 := hposstate)
            · exact hrstate

          let ⟨negstate, hnegstate⟩ : { out // posstate.IsExtensionBy out upper (mark.meet .inverted) h } :=
            if hmark : mark.has true then
              let res :=
                posstate.addGateNeg upper h heq
                  (by apply toCNF.BiMark.has_of_le hlstate''.trueAt; simp [hmark])
                  (by apply toCNF.BiMark.has_of_le hrstate''.trueAt; simp [hmark])
              ⟨res.val, toCNF.State.IsExtensionBy_le res.property (by simp)⟩
            else
              ⟨posstate, by
                apply toCNF.State.IsExtensionBy_rfl
                · assumption
                · simp at hmark
                  simp [toCNF.BiMark.le_iff, hmark]
                · simpa [posstate.cache.hmarks]
              ⟩

            have hposstate' : rstate.IsExtensionBy negstate upper (mark.meet .uninverted) (by omega) := by
              apply toCNF.State.IsExtensionBy_trans_left (h23 := hnegstate)
              · exact hposstate

            have hmarkstate : rstate.IsExtensionBy negstate upper mark (by omega) := by
              rw [show mark = (mark.meet .uninverted).join (mark.meet .inverted) by simp [toCNF.BiMark.ext_iff]]
              apply toCNF.State.IsExtensionBy_join hposstate' ?_ (toCNF.BiMark.le_rfl)
              apply toCNF.State.IsExtensionBy_trans_right (h12 := hposstate) (h23 := hnegstate)

            ⟨negstate, hmarkmeet <| toCNF.State.IsExtensionBy_trans_right (h12 := hlstate') (h23 := hmarkstate)⟩
  termination_by upper
  decreasing_by all_goals omega

/--
The node that we started CNF conversion at will always be marked as visited in the CNF cache.
-/
theorem toCNF.go_marks :
    mark ≤ (go aig start mark h state).val.cache.marks[start]'(by have := (go aig start mark h state).val.cache.hmarks; omega) :=
  (go aig start mark h state).property.trueAt

/--
The CNF returned by `go` will always be SAT at `cnfSatAssignment`.
-/
theorem toCNF.go_sat (aig : AIG Nat) (start : Nat) (mark : BiMark) (h1 : start < aig.decls.size) (assign1 : Nat → Bool)
    (state : toCNF.State aig) :
    (go aig start mark h1 state).val.Sat (cnfSatAssignment aig assign1)  := by
  have := (go aig start mark h1 state).val.inv assign1
  rw [State.sat_iff]
  simp [this]

theorem toCNF.go_as_denote' (aig : AIG Nat) (start) (mark) (inv) (h1) (assign1) :
    ⟦aig, ⟨start, inv, h1⟩, assign1⟧ → (go aig start mark h1 (.empty aig)).val.eval (cnfSatAssignment aig assign1) := by
  have := go_sat aig start mark h1 assign1 (.empty aig)
  simp only [State.Sat, CNF.sat_def] at this
  simp [this]

/--
Connect SAT results about the CNF to SAT results about the AIG.
-/
theorem toCNF.go_as_denote (aig : AIG Nat) (start) (mark) (h1) (assign1) :
    ((⟦aig, ⟨start, inv, h1⟩, assign1⟧ && (go aig start mark h1 (.empty aig)).val.eval (cnfSatAssignment aig assign1)) = sat?)
      →
    (⟦aig, ⟨start, inv, h1⟩, assign1⟧ = sat?) := by
  have := go_as_denote' aig start mark inv h1 assign1
  by_cases CNF.eval (cnfSatAssignment aig assign1) (go aig start mark h1 (State.empty aig)).val.cnf <;> simp_all

/--
Connect SAT results about the AIG to SAT results about the CNF.
-/
theorem toCNF.denote_as_go {assign : Nat → Bool} :
    (⟦aig, ⟨start, inv, h1⟩, projectLeftAssign aig assign⟧ = false)
      →
    CNF.eval assign (((go aig start (.of inv) h1 (.empty aig)).val.cnf.add [(start, !inv)])) = false := by
  intro h
  match heval1 : (go aig start (.of inv) h1 (State.empty aig)).val.cnf.eval assign with
  | true =>
    simp
    intro hassign
    have heval2 := (go aig start (.of inv) h1 (.empty aig)).val.cache.inv
    specialize heval2 assign heval1 start inv h1 (BiMark.has_of_le go_marks (by simp))
    simp [hassign, show ∀ b, true ≤ b ↔ b by decide, h] at heval2
  | false =>
    simp [heval1]

/--
An AIG is unsat iff its CNF is unsat.
-/
public theorem toCNF_equisat (entry : Entrypoint Nat) : (toCNF entry).Unsat ↔ entry.Unsat := by
  simp only [toCNF]
  constructor
  · intro h assign1
    apply toCNF.go_as_denote (mark := .of entry.ref.invert)
    specialize h (toCNF.cnfSatAssignment entry.aig assign1)
    rcases entry with ⟨_, ⟨_, _ | _, hgate⟩⟩ <;> simpa [hgate] using h
  · intro h assign
    apply toCNF.denote_as_go
    specialize h (toCNF.projectLeftAssign entry.aig assign)
    assumption

end AIG

end Sat
end Std
