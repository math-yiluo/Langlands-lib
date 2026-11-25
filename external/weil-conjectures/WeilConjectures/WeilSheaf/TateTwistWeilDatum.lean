/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.VerdierDualLocalization
public import WeilConjectures.WeilSheaf.TateTwistCohomology
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedStrSingleShift
public import WeilConjectures.CategoryTheory.WeilEquivariance

/-!
# The Frobenius structure of the Tate twist `ℚ̄_ℓ(m)[n]`

The Tate twist `ℚ̄_ℓ(m) = ℚ̄_ℓ ⊗ ℚ̄_ℓ(m)` of the constant Weil complex is the constant Weil twist
`ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ}` placed in degree `0`, as a Weil complex
(`AlgebraicGeometry.WeilComplex.tateTwistObjAdicConstantWeilIso`). Being an isomorphism of Weil
complexes, it is Frobenius equivariant for the derived structure isomorphisms, and so is its
shift (`AlgebraicGeometry.WeilComplex.isWeilEquivariant_tateTwistObjAdicConstantWeilIso_shift`).
Together with `CategoryTheory.Endofunctor.IsoAlgebra.derivedStrIso_hom_app_singleFunctor_obj`
and `derivedStrIso_hom_app_shift`, this reads the Frobenius structure of `ℚ̄_ℓ(m)[n]` as the shift
of `χ_ℓ(σ)ᵐ` times the structure of `ℚ̄_ℓ`
(`AlgebraicGeometry.WeilSheaf.constantTwist_obj_str_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

open ProEtaleWeilSheaf

variable (k₀ l X) in
/-- **The Tate twist of the constant Weil complex is a constant Weil twist in degree `0`**:
`ℚ̄_ℓ(m) ≅ (ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ})[0]` as Weil complexes. -/
noncomputable def tateTwistObjAdicConstantWeilIso (m : ℤ) :
    (tateTwist k₀ l X m).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) ≅
      WeilSheaf.toComplex.obj
        ((WeilSheaf.adicConstant k₀ l X).constantTwist (WeilSheaf.cyclotomicUnit k₀ l ^ m)) :=
  tensorLisseToComplexIso (WeilSheaf.tateTwistSheaf k₀ l X m)
      (WeilSheaf.isLisse_tateTwistSheaf k₀ l X m) (WeilSheaf.adicConstant k₀ l X) ≪≫
    WeilSheaf.toComplex.mapIso (ObjectProperty.isoMk _
      (WeilSheaf.tensorObjObjIsoOfIso _ _ _ (WeilSheaf.tateTwistSheafObjIso k₀ l X m)
          (constantTwistOneObjIso _).symm ≪≫
        constantTwistCongrIso (mul_one _) _ ≪≫
        ((WeilSheaf.adicConstant k₀ l X).constantTwistObjIso _).symm))

set_option linter.unusedSectionVars false in
/-- Isomorphisms of Weil complexes are Frobenius equivariant for the derived structure
isomorphisms. -/
lemma isWeilEquivariant_forget_map {M N : WeilComplex k₀ l X} (u : M ⟶ N) :
    IsWeilEquivariant (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory
      ((IsoAlgebra.derivedStrIso _).hom.app M.obj) ((IsoAlgebra.derivedStrIso _).hom.app N.obj)
      (forget.map u) :=
  (IsoAlgebra.derivedStrIso _).hom.naturality u.hom

/-- The identification `ℚ̄_ℓ(m) ≅ (ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ})[0]` is Frobenius equivariant. -/
lemma isWeilEquivariant_tateTwistObjAdicConstantIso (m : ℤ) :
    IsWeilEquivariant (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory
      ((IsoAlgebra.derivedStrIso _).hom.app
        ((tateTwist k₀ l X m).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X))).obj)
      ((IsoAlgebra.derivedStrIso _).hom.app (WeilSheaf.toComplex.obj
        ((WeilSheaf.adicConstant k₀ l X).constantTwist (WeilSheaf.cyclotomicUnit k₀ l ^ m))).obj)
      (forget.map (tateTwistObjAdicConstantWeilIso k₀ l X m).hom) :=
  isWeilEquivariant_forget_map _

/-- The shifted identification `ℚ̄_ℓ(m)[n] ≅ (ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ})[n]` is Frobenius equivariant. -/
lemma isWeilEquivariant_tateTwistObjAdicConstantWeilIso_shift (m n : ℤ) :
    IsWeilEquivariant (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory
      ((IsoAlgebra.derivedStrIso _).hom.app
        (((tateTwist k₀ l X m).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦n⟧).obj)
      ((IsoAlgebra.derivedStrIso _).hom.app ((WeilSheaf.toComplex.obj
        ((WeilSheaf.adicConstant k₀ l X).constantTwist
          (WeilSheaf.cyclotomicUnit k₀ l ^ m)))⟦n⟧).obj)
      (forget.map ((tateTwistObjAdicConstantWeilIso k₀ l X m).hom⟦n⟧')) :=
  isWeilEquivariant_forget_map _

end WeilComplex

end AlgebraicGeometry
