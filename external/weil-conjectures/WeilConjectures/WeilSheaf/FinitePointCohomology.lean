/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedOpenImmersionUnit
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.StalkFrobeniusPow

/-!
# Weil sheaves on a finite étale `k₀`-scheme

Let `P` be a finite étale `k₀`-scheme, for instance the spectrum of the residue field of a closed
point of a `k₀`-scheme of finite type. Its geometric fiber `P̄ = P ⊗ k̄` is a finite disjoint union
of copies of `Spec k̄`. For a Weil sheaf `G` on `P`:

- the global sections `Γ(P̄, G)` surject onto every geometric stalk, Frobenius-equivariantly for
  the local Frobenius `F_x = Fr^{deg x}` at a closed point `x`, so every eigenvalue of `F_x` is the
  `deg x`-th power of an eigenvalue of the Frobenius of `Γ(P̄, G)`
  (`AlgebraicGeometry.WeilSheaf.exists_hasEigenvalue_globalSections_of_hasEigenvalue_stalk`);
- if `Γ(P̄, G)` is `ι`-pure of weight `w` over `k₀`, then `G` is punctually `ι`-pure of weight
  `w` (`AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_of_isPureOfWeightOver_globalSections`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The geometric point over a closed point is a section of the structure morphism of the
geometric fiber over `k̄`. -/
@[reassoc (attr := simp)]
lemma Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberToAlgebraicClosure'
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X.finitePoints) :
    f.geometricFiberPointOfFinitePoint x ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ := by
  let := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  exact f.geometricFiberPoint_comp_geometricFiberToAlgebraicClosure (K := X.residueField x.1)
    IsAlgClosed.lift (X.fromSpecResidueField x.1) (f.specMap_residueFieldAlgebraMap x.1).symm


/-- For a finite étale `f : X ⟶ Spec k`, the geometric fiber `X̄ ⟶ Spec k̄` is finite étale, so
its section at the geometric point over a closed point is an open immersion. -/
lemma Scheme.Hom.isOpenImmersion_geometricFiberPointOfFinitePoint {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Etale f] (x : X.finitePoints) :
    IsOpenImmersion (f.geometricFiberPointOfFinitePoint x) := by
  have : Etale f.geometricFiberToAlgebraicClosure := inferInstanceAs (Etale (pullback.snd _ _))
  have : IsOpenImmersion (f.geometricFiberPointOfFinitePoint x ≫
      f.geometricFiberToAlgebraicClosure) := by
    rw [geometricFiberPointOfFinitePoint_comp_geometricFiberToAlgebraicClosure']
    infer_instance
  exact FormallyUnramified.isOpenImmersion_of_comp f.geometricFiberToAlgebraicClosure _

/-- For a finite `f : X ⟶ Spec k`, the geometric fiber `X̄ ⟶ Spec k̄` is finite, hence separated,
so its section at the geometric point over a closed point is a closed immersion. -/
lemma Scheme.Hom.isClosedImmersion_geometricFiberPointOfFinitePoint {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsFinite f] (x : X.finitePoints) :
    IsClosedImmersion (f.geometricFiberPointOfFinitePoint x) := by
  have : IsFinite f.geometricFiberToAlgebraicClosure :=
    inferInstanceAs (IsFinite (pullback.snd _ _))
  have : IsClosedImmersion (f.geometricFiberPointOfFinitePoint x ≫
      f.geometricFiberToAlgebraicClosure) := by
    rw [geometricFiberPointOfFinitePoint_comp_geometricFiberToAlgebraicClosure']
    infer_instance
  exact IsClosedImmersion.of_comp _ f.geometricFiberToAlgebraicClosure
namespace WeilSheaf

open scoped AlgebraicGeometry.ProEtale

section Surjective

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The restriction `Γ(X̄, F) ⟶ F_s` of global sections to the stalk at a geometric point `s`
which is an open immersion with closed range is surjective: the unit `F ⟶ s_* s^* F` is a split
epimorphism, sections over the clopen point extending by zero
(`AlgebraicGeometry.ProEtale.isSplitEpi_adicUpperStarLowerStarAdjunction_unit_app`). -/
theorem surjective_globalSectionsToStalkObj (F : WeilSheaf k₀ l X)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [IsOpenImmersion s] (hs : IsClosed (Set.range s.base)) :
    Function.Surjective
      ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom := by
  have := ProEtale.isSplitEpi_adicUpperStarLowerStarAdjunction_unit_app l s hs F.obj.carrier
  obtain ⟨σ, hσ⟩ : ∃ σ, σ ≫ (ProEtale.adicUpperStarLowerStarAdjunction l s).unit.app
      F.obj.carrier = 𝟙 _ := ⟨_, IsSplitEpi.id _⟩
  have h := congrArg Mod.Hom.hom hσ
  rw [Mod.comp_hom', ProEtale.adicUpperStarLowerStarAdjunction,
    Adjunction.modAdjunction_unit_app_hom, Mod.id_hom'] at h
  have key : ((ProEtale.globalSectionsLowerStarIso _ s).inv.app _ ≫ (Sheaf.Γ _ _).map σ.hom) ≫
      F.globalSectionsToStalkObj s = 𝟙 _ := by
    rw [globalSectionsToStalkObj, Category.assoc, ← Functor.map_comp_assoc, h]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  intro y
  refine ⟨_, (toModuleCat_map_comp_apply ((ProEtale.globalSectionsLowerStarIso _ s).inv.app _ ≫
    (Sheaf.Γ _ _).map σ.hom) _ y).symm.trans ?_⟩
  rw [key, CategoryTheory.Functor.map_id]
  rfl

/-- If the restriction `Γ(X̄, F) ⟶ F_s` to the stalk at a geometric point `s` with
`s ≫ Frᵐ = σᵐ ≫ s`, `m ≥ 1`, is surjective, every eigenvalue of the Frobenius of `F_s` relative
to `𝔽_{qᵐ}` is the `m`-th power of an eigenvalue of the Frobenius of `Γ(X̄, F)`. -/
theorem exists_hasEigenvalue_globalSections_of_surjective (F : WeilSheaf k₀ l X)
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hm : 1 ≤ m)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (hsurj : Function.Surjective
      ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom)
    {β : PadicAlgCl l} (hβ : (F.stalkAt s m hs).frobeniusEnd.HasEigenvalue β) :
    ∃ α : PadicAlgCl l, F.globalSections.frobeniusEnd.HasEigenvalue α ∧ α ^ m = β := by
  have hsurj' : Function.Surjective (F.globalSectionsToStalkAt s m hs) := fun y ↦
    (hsurj y).imp fun a ha ↦ (F.globalSectionsToStalkAt_apply s m hs a).trans ha
  exact (Module.End.HasEigenvalue.of_surjective_comp_eq hsurj'
    (F.globalSectionsToStalkAt_comp_frobeniusEnd_pow s m hm hs) hβ).exists_pow_eq hm

end Surjective

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {P : Scheme.{u}} [P.Over (Spec (CommRingCat.of k₀))]
  [IsFinite (P ↘ Spec (CommRingCat.of k₀))] [Etale (P ↘ Spec (CommRingCat.of k₀))]

/-- On a finite étale `k₀`-scheme `P`, every eigenvalue `β` of the local Frobenius `F_x` of a
Weil sheaf `G` at a closed point `x` is `α ^ deg x` for an eigenvalue `α` of the Frobenius of the
global sections `Γ(P̄, G)`: the restriction `Γ(P̄, G) ⟶ G_x̄` is surjective, `x̄` being a clopen
point of the finite discrete scheme `P̄`, and it intertwines `Fr^{deg x}` with `F_x`. -/
theorem exists_hasEigenvalue_globalSections_of_hasEigenvalue_stalk (G : WeilSheaf k₀ l P)
    (x : P.finitePoints) {β : PadicAlgCl l} (hβ : (G.stalk x).frobeniusEnd.HasEigenvalue β) :
    ∃ α : PadicAlgCl l, G.globalSections.frobeniusEnd.HasEigenvalue α ∧
      α ^ (P ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 = β := by
  have := Scheme.Hom.isOpenImmersion_geometricFiberPointOfFinitePoint
    (P ↘ Spec (CommRingCat.of k₀)) x
  have := Scheme.Hom.isClosedImmersion_geometricFiberPointOfFinitePoint
    (P ↘ Spec (CommRingCat.of k₀)) x
  exact G.exists_hasEigenvalue_globalSections_of_surjective _ _
    (Nat.one_le_iff_ne_zero.2 ((P ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2))
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ x)
    (G.surjective_globalSectionsToStalkObj _ (Scheme.Hom.isClosedEmbedding _).isClosed_range) hβ

/-- On a finite étale `k₀`-scheme `P`, if the global sections `Γ(P̄, G)` of a Weil sheaf are
`ι`-pure of weight `w` over `k₀`, then `G` is punctually `ι`-pure of weight `w`: an eigenvalue of
`F_x` is `α ^ deg x` with `|ι α| = q^{w/2}`, and `q_x = q ^ deg x`. -/
theorem isPunctuallyPureOfWeight_of_isPureOfWeightOver_globalSections {ι : PadicAlgCl l →+* ℂ}
    {G : WeilSheaf k₀ l P} {w : ℝ} (h : G.globalSections.IsPureOfWeightOver k₀ ι w) :
    G.IsPunctuallyPureOfWeight ι w := by
  intro x β hβ
  obtain ⟨α, hα, rfl⟩ := exists_hasEigenvalue_globalSections_of_hasEigenvalue_stalk G x hβ
  rw [Scheme.Hom.residueCard, map_pow, norm_pow, h α hα, Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]

end WeilSheaf

end AlgebraicGeometry
