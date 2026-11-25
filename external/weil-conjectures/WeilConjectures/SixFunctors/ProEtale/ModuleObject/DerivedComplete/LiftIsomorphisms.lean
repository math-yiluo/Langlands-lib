/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms

/-!
# Lifting isomorphisms of reductions by König's lemma

Let `K` and `L` be complexes of `𝒪_{E,X}`-module objects on `X_proét` with `L` derived complete,
and write `red_n` for the derived reduction modulo `ℓⁿ`. If for every `n ≥ 1` the reductions
`red_n K` and `red_n L` are isomorphic and there are only finitely many morphisms
`red_n K ⟶ red_n L`, then there is a morphism `f : K ⟶ L` whose reductions `red_n f` are all
isomorphisms (`ProEtale.exists_forall_isIso_derivedReduction_map`).

The isomorphisms `red_{n+1} K ≅ red_{n+1} L` form an inverse system of nonempty finite sets under
reduction `red_{n+1} ⟶ red_n` (`Mod.derivedExtendScalarsReduction`), which has a compatible
family by König's lemma (`nonempty_sections_of_finite_inverse_system`); a compatible family
lifts to `L` (`ProEtale.exists_derivedReduction_map_eq`). No choice of the isomorphisms is
canonical: this is used to prove *properties* (e.g. dualizability), never to construct data.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

/-- A tower with finite morphism sets and isomorphism-preserving transition maps has a
compatible family of isomorphisms whenever its objects are isomorphic at every stage. -/
private lemma exists_compatible_isIso_homs_of_finite {C : ℕ → Type*} [∀ n, Category (C n)]
    {K L : ∀ n, C n} (hfin : ∀ n, Finite (K n ⟶ L n))
    (hne : ∀ n, Nonempty (K n ≅ L n))
    (r : ∀ n, (K (n + 1) ⟶ L (n + 1)) → (K n ⟶ L n))
    (hiso : ∀ n s, IsIso s → IsIso (r n s)) :
    ∃ t : ∀ n, K n ⟶ L n, (∀ n, IsIso (t n)) ∧ ∀ n, r n (t (n + 1)) = t n := by
  let ri (n : ℕ) (s : K (n + 1) ≅ L (n + 1)) : K n ≅ L n :=
    @asIso _ _ _ _ (r n s.hom) (hiso n s.hom inferInstance)
  let F : ℕᵒᵖ ⥤ Type _ :=
    Functor.ofOpSequence (X := fun n ↦ K n ≅ L n) fun n ↦ TypeCat.ofHom (ri n)
  have : ∀ j, Finite (F.obj j) := fun j ↦ by
    have := hfin j.unop
    exact Finite.of_injective (fun e : K j.unop ≅ L j.unop ↦ e.hom)
      fun _ _ h ↦ Iso.ext h
  have : ∀ j, Nonempty (F.obj j) := fun j ↦ hne j.unop
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n ↦ (s (op n)).hom, fun n ↦ inferInstance, fun n ↦ ?_⟩
  have h := hs (homOfLE (Nat.le_add_right n 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact congrArg Iso.hom h

/-- If compatible families of morphisms lift, a compatible family of isomorphisms gives a
lift whose image is an isomorphism at every stage. -/
private lemma exists_isIso_maps_of_finite {C : ℕ → Type*} [∀ n, Category (C n)]
    {K L : ∀ n, C n} (hfin : ∀ n, Finite (K n ⟶ L n))
    (hne : ∀ n, Nonempty (K n ≅ L n))
    (r : ∀ n, (K (n + 1) ⟶ L (n + 1)) → (K n ⟶ L n))
    (hiso : ∀ n s, IsIso s → IsIso (r n s)) {S : Type*} {map : S → ∀ n, K n ⟶ L n}
    (hlift : ∀ t : ∀ n, K n ⟶ L n,
      (∀ n, r n (t (n + 1)) = t n) → ∃ f, ∀ n, map f n = t n) :
    ∃ f, ∀ n, IsIso (map f n) := by
  obtain ⟨t, hi, ht⟩ := exists_compatible_isIso_homs_of_finite hfin hne r hiso
  obtain ⟨f, hf⟩ := hlift t ht
  exact ⟨f, fun n ↦ (hf n) ▸ hi n⟩

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

open scoped CategoryTheory.Obj

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The reduction `red_n s` of a morphism `s : red_{n+1} K ⟶ red_{n+1} L` along
`𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ`. -/
noncomputable abbrev derivedReductionStep (n : ℕ)
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (s : (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L) :
    (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj L :=
  Mod.derivedExtendScalarsReduction _ (integersModPowTransition X ℓ E n) _
    (integersModPowReduction_comp_integersModPowTransition X ℓ E n) s

lemma isIso_derivedReductionStep (n : ℕ)
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (s : (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L)
    [IsIso s] : IsIso (derivedReductionStep n s) := by
  dsimp only [derivedReductionStep, Mod.derivedExtendScalarsReduction]
  infer_instance

/-- A reduction step is compatible with the transition maps after restricting scalars. -/
private lemma map_comp_reductionTransition_derivedReductionStep (n : ℕ)
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (s : (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L) :
    (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.map s ≫
        reductionTransition E n L =
      reductionTransition E n K ≫
        (Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory.map
          (derivedReductionStep n s) :=
  Mod.map_comp_derivedReductionTransition_app
    (integersModPowReduction X ℓ E (n + 1)) (integersModPowTransition X ℓ E n)
    (integersModPowReduction X ℓ E n)
    (integersModPowReduction_comp_integersModPowTransition X ℓ E n) (A := L) (B := K) s

/-- **Lifting isomorphisms of reductions** (König's lemma): if `L` is derived complete, and for
every `n` the reductions `red_{n+1} K`, `red_{n+1} L` are isomorphic with finitely many morphisms
between them, there is `f : K ⟶ L` all of whose reductions are isomorphisms. -/
theorem exists_forall_isIso_derivedReduction_map
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    (hfin : ∀ n : ℕ, Finite
      ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L))
    (hne : ∀ n : ℕ, Nonempty
      ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ≅
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L)) :
    ∃ f : K ⟶ L, ∀ n : ℕ,
      IsIso ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map
        f) := by
  refine exists_isIso_maps_of_finite hfin hne
    (fun n ↦ derivedReductionStep (X := X) (ℓ := ℓ) (E := E) (n + 1) (K := K) (L := L))
    (fun n s hs ↦ isIso_derivedReductionStep (n + 1) s) ?_
  intro t ht
  apply exists_derivedReduction_map_eq (X := X) (ℓ := ℓ) (E := E) (K := K) (L := L) hL t
  intro n
  rw [← ht n]
  exact map_comp_reductionTransition_derivedReductionStep (n + 1) (t (n + 1))

end AlgebraicGeometry.ProEtale
