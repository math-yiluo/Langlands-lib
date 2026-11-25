/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Kernel of the sheafified sectionwise quotient

Source: Stacks Project, Sheaves of Modules, Tag 01AH; Sites, Tags 00WB and 00WK
(blueprint: lem-weil-pbc-sheaf-cokernel-local-image).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- The kernel of the map to the sheafified sectionwise quotient consists precisely of
sections locally in the image. The quotient map is epic and annihilates the original map.
`X` is a ringed space with module sheaves over `moduleRings X`. The presheaf
`cokernel φ.val` is the sectionwise quotient, since presheaf-module evaluation preserves
cokernels. The equality `hq` ties `q` to the canonical composite: the quotient projection
followed by the unit of module sheafification; it is construction data, rather than a
condition on the original morphism.

Source: Stacks Project, Sheaves of Modules, Tag 01AH; Sites, Tags 00WB and 00WK
(blueprint: lem-weil-pbc-sheaf-cokernel-local-image).

Proof:
1. The equality `hq` and the cokernel condition show that `φ ≫ q = 0`, by
faithfulness of the forgetful functor from module sheaves.
2. If two morphisms agree after `q`, the sheafification adjunction identifies them
with presheaf morphisms out of the cokernel. Cancel its epic projection and use
injectivity of the adjunction's hom equivalence. This proves `Epi q`.
3. Evaluation preserves finite colimits, so evaluating the cokernel short complex
on any open gives an exact complex of modules. A section killed by the quotient
projection therefore has a preimage under the corresponding component of `φ`.
4. The underlying additive-group sheafification unit is locally injective. If
`q(s) = 0`, its equalizer sieve for the quotient class of `s` and zero covers the
open. Naturality and Step 3 give a preimage on a neighborhood of each point.
Conversely, local preimages and Step 1 make `q(s)` locally zero; separatedness of
the sheafified quotient makes it zero. This also applies to the empty open. -/
theorem sheafified_cokernel_local_image (X : RingedSpace.{u})
    {F G : SheafOfModules.{u} (moduleRings X)} (φ : F ⟶ G)
    (q : G ⟶ (PresheafOfModules.sheafification (𝟙 (moduleRings X).obj)).obj (cokernel φ.val))
    (hq : q.val = cokernel.π φ.val ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 (moduleRings X).obj)).unit.app
        (cokernel φ.val)) :
    (∀ (V : Opens X) (s : G.val.obj (op V)),
      q.val.app (op V) s = 0 ↔
        ∀ x : X, x ∈ V → ∃ (W : Opens X) (hWV : W ≤ V),
          x ∈ W ∧ ∃ t : F.val.obj (op W),
            φ.val.app (op W) t = G.val.map (homOfLE hWV).op s) ∧
      Epi q ∧ φ ≫ q = 0 := by
  let R := moduleRings X
  let P := cokernel φ.val
  let p := cokernel.π φ.val
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P
  have hzero : φ ≫ q = 0 := by
    apply (SheafOfModules.forget R).map_injective
    change φ.val ≫ q.val = 0
    rw [hq, ← Category.assoc, cokernel.condition, zero_comp]
  have hepi : Epi q := by
    constructor
    intro H a b hab
    apply (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).injective
    apply (cancel_epi p).mp
    change p ≫ η ≫ a.val = p ≫ η ≫ b.val
    rw [← Category.assoc, ← Category.assoc, ← hq]
    exact congrArg SheafOfModules.Hom.val hab
  have hexact (W : Opens X) :
      ∀ s : G.val.obj (op W), p.app (op W) s = 0 →
        ∃ t : F.val.obj (op W), φ.val.app (op W) t = s := by
    let S := ShortComplex.mk φ.val p (cokernel.condition φ.val)
    have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel φ.val)
    have h := hS.map (PresheafOfModules.evaluation R.obj (op W))
    exact (ShortComplex.moduleCat_exact_iff _).mp h
  refine ⟨?_, hepi, hzero⟩
  intro V s
  constructor
  · intro hs
    have hs' :
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf).app
          (op V) (p.app (op V) s) =
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf).app
          (op V) 0 := by
      rw [hq] at hs
      change (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf).app
        (op V) (p.app (op V) s) = 0 at hs
      exact hs.trans (map_zero _).symm
    have hc := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf) _ _ hs'
    rw [Opens.mem_grothendieckTopology] at hc
    intro x hx
    obtain ⟨W, i, hi, hxW⟩ := hc x hx
    refine ⟨W, i.le, hxW, ?_⟩
    apply hexact W
    have hn := PresheafOfModules.naturality_apply p i.op s
    change P.map i.op (p.app (op V) s) = P.map i.op 0 at hi
    rw [map_zero] at hi
    exact hn.trans hi
  · intro hs
    let T := (PresheafOfModules.sheafification (𝟙 R.obj)).obj P
    have hc : Presheaf.equalizerSieve (F := T.val.presheaf) (q.val.app (op V) s)
        (0 : T.val.obj (op V)) ∈ Opens.grothendieckTopology X V := by
      rw [Opens.mem_grothendieckTopology]
      intro x hx
      obtain ⟨W, hWV, hxW, t, ht⟩ := hs x hx
      refine ⟨W, homOfLE hWV, ?_, hxW⟩
      change T.val.map (homOfLE hWV).op (q.val.app (op V) s) =
        T.val.map (homOfLE hWV).op 0
      rw [map_zero, ← PresheafOfModules.naturality_apply q.val, ← ht]
      have hz := congrArg (fun f ↦ f.val.app (op W) t) hzero
      exact hz
    exact T.isSheaf.isSeparated _ _ hc _ _ (fun _ _ hf ↦ hf)

end AlgebraicGeometry.RingedSpace
