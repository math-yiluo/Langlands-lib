/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Constructible `ℓ`-adic sheaves on the spectrum of an algebraically closed field

Let `K` be an algebraically closed field. Every pro-étale cover of `Spec K` has a section: a
weakly étale scheme over `K` with a point has a `K`-point
(`AlgebraicGeometry.exists_comp_eq_id_of_weaklyEtale`). Hence a lisse `ℓ`-adic sheaf on
`Spec K`, trivialised on some pro-étale cover, is already trivial: it is a finite direct sum
of copies of the constant `ℓ`-adic sheaf `ℚ̄_ℓ`. A constructible sheaf on `Spec K` is lisse,
the only nonempty stratum being `Spec K` itself, and its global sections are
finite-dimensional, the global sections of `ℚ̄_ℓ` on the point `Spec K` being `ℚ̄_ℓ`.

## Main results

- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_biproduct_of_isAlgClosed`: a lisse
  sheaf on `Spec K` is isomorphic to `ℚ̄_ℓⁿ`.
- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.isAdicLisseSheaf_of_isField`: a
  constructible sheaf on the spectrum of a field is lisse.
- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.finiteDimensional_globalSections`: the
  global sections of a constructible sheaf on `Spec K` are finite-dimensional.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- A lisse `ℓ`-adic sheaf on the spectrum of an algebraically closed field `K` is a finite
direct sum of copies of `ℚ̄_ℓ`: a member `f : V ⟶ Spec K` of a trivialising pro-étale cover
with `V` nonempty has a section `σ`, and `F ≅ σ^* f^* F ≅ σ^* ℚ̄_ℓ,Vⁿ ≅ ℚ̄_ℓⁿ`. -/
theorem IsAdicLisseSheaf.exists_iso_biproduct_of_isAlgClosed
    {F : AdicSheaf l (Spec (.of K))}
    (hF : IsAdicLisseSheaf F) :
    ∃ n : ℕ, Nonempty (F ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K))) := by
  obtain ⟨R, hR, h⟩ := hF
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hR' : _ ∈ Scheme.precoverage (@WeaklyEtale : MorphismProperty Scheme.{u}) _ :=
    (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from inf_le_right) _ hR
  rw [Scheme.ofArrows_mem_precoverage_iff (@WeaklyEtale : MorphismProperty Scheme.{u})] at hR'
  obtain ⟨i, v, -⟩ := hR'.1 (IsLocalRing.closedPoint K)
  have : WeaklyEtale (f i) := hR'.2 i
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (f i) v
  obtain ⟨n, ⟨e⟩⟩ := h (f i) (.mk i)
  obtain ⟨e'⟩ := nonempty_upperStar_iso_biproduct σ ⟨adicUpperStarUnitIso l σ⟩ e
  exact ⟨n, ⟨((adicUpperStarId l _).app F).symm ≪≫ (adicUpperStarCongr l hσ.symm).app F ≪≫
    (adicUpperStarComp l _ _).app F ≪≫ e'⟩⟩

omit [IsAlgClosed K] in
/-- A constructible `ℓ`-adic sheaf on the spectrum of a field is lisse: the stratum through the
point is an immersion into the point, hence an isomorphism. -/
theorem IsAdicConstructibleSheaf.isAdicLisseSheaf_of_isField
    {F : AdicSheaf l (Spec (.of K))}
    (hF : IsAdicConstructibleSheaf F) : IsAdicLisseSheaf F := by
  obtain ⟨W, j, hj, ⟨w, -⟩, hW⟩ := hF (IsLocalRing.closedPoint K)
  obtain ⟨ι, -, Z, i, hi, -, hcover, h⟩ := hW
  obtain ⟨k, ⟨z, -⟩, -⟩ := hcover w
  have : Nonempty (Z k) := ⟨z⟩
  have := hi k
  have : IsIso (i k ≫ j) := IsImmersion.isIso_of_nonempty _
  have e : (inv (i k ≫ j) ≫ i k) ≫ j = 𝟙 _ := by simp
  exact ((h k).upperStar (inv (i k ≫ j))).of_iso
    (((adicUpperStarComp l (inv (i k ≫ j)) (i k)).app _).symm ≪≫
      ((adicUpperStarComp l (inv (i k ≫ j) ≫ i k) j).app F).symm ≪≫
      (adicUpperStarCongr l e).app F ≪≫ (adicUpperStarId l _).app F)

/-- The global sections of the constant `ℓ`-adic sheaf on the spectrum of a field are
finite-dimensional: they are the continuous functions on the one-point space `Spec K`. -/
lemma finiteDimensional_globalSections_adicConstantSheaf (K : Type u) [Field K] :
    FiniteDimensional (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj
        (adicConstantSheaf l (Spec (.of K))))) := by
  let e := (WeilCoefficients.toModuleCat l).mapIso
    ((Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId (Spec (.of K)))).app
      (adicConstantSheaf l (Spec (.of K))))
  suffices h : Module.Finite (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l (Spec (.of K)))))) from
    @Module.Finite.equiv _ _ _ _ _ _ _ _ h e.toLinearEquiv.symm
  let φ : (WeilCoefficients.toModuleCat l).obj (ModuleCat.of _
      (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l (Spec (.of K))))) →ₗ[PadicAlgCl l]
      PadicAlgCl l :=
    { toFun x := (ULift.down x).1 (IsLocalRing.closedPoint K)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hφ : Function.Injective φ := fun x y h ↦ ULift.ext <| Subtype.ext <|
    ContinuousMap.ext fun p ↦ by
      obtain rfl : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact h
  exact Module.Finite.of_injective φ hφ

/-- The global sections of a constructible `ℓ`-adic sheaf on the spectrum of an algebraically
closed field are finite-dimensional: the sheaf is a finite direct sum of copies of `ℚ̄_ℓ`. -/
theorem IsAdicConstructibleSheaf.finiteDimensional_globalSections
    {F : AdicSheaf l (Spec (.of K))}
    (hF : IsAdicConstructibleSheaf F) :
    FiniteDimensional (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj F.X)) := by
  obtain ⟨n, ⟨e⟩⟩ := hF.isAdicLisseSheaf_of_isField.exists_iso_biproduct_of_isAlgClosed
  have : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let G := Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l) ⋙
    WeilCoefficients.toModuleCat l
  let e' : G.obj F.X ≅ ModuleCat.of _ (Fin n → G.obj (adicConstantSheaf l (Spec (.of K)))) :=
    G.mapIso ((AdicSheaf.forget _).mapIso e ≪≫
      (AdicSheaf.forget _).mapBiproduct (fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K)))) ≪≫
      G.mapBiproduct (fun _ : Fin n ↦ adicConstantSheaf l (Spec (.of K))) ≪≫
      ModuleCat.biproductIsoPi (fun _ : Fin n ↦ G.obj (adicConstantSheaf l (Spec (.of K))))
  have : FiniteDimensional (PadicAlgCl l) (G.obj (adicConstantSheaf l (Spec (.of K)))) :=
    finiteDimensional_globalSections_adicConstantSheaf K
  exact LinearEquiv.finiteDimensional e'.toLinearEquiv.symm

end ProEtale

end AlgebraicGeometry
