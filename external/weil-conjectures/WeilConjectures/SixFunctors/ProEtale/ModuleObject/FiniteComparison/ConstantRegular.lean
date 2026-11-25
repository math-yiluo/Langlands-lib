/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.FinitePresentationCokernel
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin.Constructible.Regular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# Constant sheaves of finite modules as finitely presented module objects

Let `T` be a finite discrete commutative ring, `X` a scheme and
`Φ = ProEtale.finiteCoefficientModEquivalence X T` the equivalence between module objects over
`Λ_X = p_X^* T̲` and sheaves of `T`-modules on `X_proét`.

* `Φ⁻¹` of the constant sheaf `T` is the free module `Λ_X`
  (`ProEtale.regularIsoInverseConstant`), and `Φ⁻¹ ∘ const` is left adjoint to `Γ ∘ Φ`
  (`ProEtale.constantSheafCompInverseAdjunction`).
* Hence `Φ⁻¹` of the constant sheaf of a finite `T`-module is finitely presented
  (`ProEtale.isFinitelyPresented_finiteCoefficientModEquivalence_inverse_obj_constantSheaf`):
  `T` is noetherian, so a finite `T`-module is the cokernel of a morphism `Tᵐ ⟶ Tⁿ`, and
  `Φ⁻¹ ∘ const` is additive and right exact.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)] {D : Type*} [Category* D]
  [Abelian D] [HasFiniteBiproducts D]

/-- An additive functor `G : D ⥤ Mod_R` with `G Λ₀ ≅ R` sends the biproduct `Λ₀ⁿ` to the free
module `Rⁿ`. -/
noncomputable def finiteFreeIsoMapBiproduct (G : D ⥤ Mod C R) [G.Additive] {Λ₀ : D}
    (e : G.obj Λ₀ ≅ regular R) (n : ℕ) :
    G.obj (⨁ fun _ : Fin n ↦ Λ₀) ≅ finiteFree R n :=
  G.mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ e

/-- An additive right exact functor `G : D ⥤ Mod_R` with `G Λ₀ ≅ R` sends the cokernel of a
morphism `Λ₀ᵐ ⟶ Λ₀ⁿ` to a finitely presented module object. -/
lemma IsFinitelyPresented.of_iso_obj_cokernel (G : D ⥤ Mod C R) [G.Additive]
    [PreservesFiniteColimits G] {Λ₀ : D} (e : G.obj Λ₀ ≅ regular R) {m n : ℕ}
    (f : (⨁ fun _ : Fin m ↦ Λ₀) ⟶ ⨁ fun _ : Fin n ↦ Λ₀) {M : Mod C R}
    (e' : M ≅ G.obj (cokernel f)) : IsFinitelyPresented R M :=
  ⟨n, m, (finiteFreeIsoMapBiproduct G e m).inv ≫ G.map f ≫ (finiteFreeIsoMapBiproduct G e n).hom,
    ⟨e' ≪≫ PreservesCokernel.iso G f ≪≫ cokernel.mapIso _ _ (finiteFreeIsoMapBiproduct G e m)
      (finiteFreeIsoMapBiproduct G e n) (by simp)⟩⟩

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- `Φ⁻¹ ∘ const ⊣ Γ ∘ Φ`: the constant sheaf functor followed by `Φ⁻¹`, for
`Φ = finiteCoefficientModEquivalence`, is left adjoint to `Φ` followed by the global sections. -/
noncomputable def constantSheafCompInverseAdjunction :
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T)) ⋙
        (finiteCoefficientModEquivalence X T).inverse ⊣
      (finiteCoefficientModEquivalence X T).functor ⋙
        (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
          (op (Scheme.ProEt.mk (𝟙 X))) :=
  (constantSheafAdj _ _ (Scheme.ProEt.isTerminalMkId X)).comp
    (finiteCoefficientModEquivalence X T).symm.toAdjunction

instance additive_constantSheafCompInverse :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T)) ⋙
      (finiteCoefficientModEquivalence X T).inverse).Additive :=
  inferInstance

/-- **`Φ⁻¹` of the constant sheaf of a finite `T`-module is finitely presented**: a finite module
over the noetherian ring `T` is the cokernel of a morphism `Tᵐ ⟶ Tⁿ`, and `Φ⁻¹ ∘ const` is
additive, right exact (a left adjoint) and sends `T` to `Λ_X`. -/
lemma isFinitelyPresented_finiteCoefficientModEquivalence_inverse_obj_constantSheaf
    (P : ModuleCat.{u + 1} (ULift.{u + 1} T)) [Module.Finite (ULift.{u + 1} T) P] :
    Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj T) X)
      ((finiteCoefficientModEquivalence X T).inverse.obj
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
          P)) := by
  obtain ⟨m, n, f, ⟨e⟩⟩ := ModuleCat.exists_iso_cokernel_of_finite P
  have : PreservesColimitsOfSize.{0, 0}
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T)) ⋙
        (finiteCoefficientModEquivalence X T).inverse) :=
    (constantSheafCompInverseAdjunction X T).leftAdjoint_preservesColimits
  exact Mod.IsFinitelyPresented.of_iso_obj_cokernel
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T)) ⋙
      (finiteCoefficientModEquivalence X T).inverse)
    (regularIsoInverseConstant T X).symm f
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T)) ⋙
      (finiteCoefficientModEquivalence X T).inverse).mapIso e)

end AlgebraicGeometry.ProEtale
