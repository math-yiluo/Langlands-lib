/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# Internal hom and pullback of pro-étale Weil sheaves commute with constant twists

`𝓗om(ℚ̄_ℓ(m)^∨, -)` is the constant twist by `χ_ℓ(σ)^m`, and the internal hom out of a fixed
sheaf and the pullback commute with constant twists, also after deriving.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedFunctorIhomFunctorTateTwistIso`
- `AlgebraicGeometry.ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompRightDerivedIhomIso`
- `AlgebraicGeometry.ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompUpperStarIso`
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

section Ihom

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- Constant twists by equal units are isomorphic functors. -/
noncomputable def constantTwistFunctorCongrIso {b c : (PadicAlgCl l)ˣ} (h : b = c) :
    constantTwist k₀ l X b ≅ constantTwist k₀ l X c :=
  eqToIso (by rw [h])

variable [Fact (ringChar k₀ ≠ l)]

/-- An isomorphism `A ≅ A'` of pro-étale Weil sheaves induces `𝓗om(A', -) ≅ 𝓗om(A, -)`. -/
noncomputable def ihomFunctorMapIsoLeft {A A' : ProEtaleWeilSheaf k₀ l X} (φ : A ≅ A') :
    ihomFunctor k₀ l X A' ≅ ihomFunctor k₀ l X A :=
  NatIso.ofComponents (ihomMapIsoLeft φ) fun f ↦ by
    apply IsoAlgebra.hom_ext
    exact (Mod.ihomMapIso ((IsoAlgebra.forget _).mapIso φ)).hom.naturality f.hom.f

variable (k₀ l X) in
/-- `𝓗om(ℚ̄_ℓ, -)` is the identity of pro-étale Weil sheaves. -/
noncomputable def ihomFunctorAdicConstantIso :
    ihomFunctor k₀ l X (adicConstant k₀ l X) ≅ 𝟭 _ :=
  NatIso.ofComponents ihomAdicConstantIso fun f ↦ by
    apply IsoAlgebra.hom_ext
    exact Mod.ihomRegularIso.hom.naturality f.hom.f

/-- `𝓗om(A ⊗ 𝓑_b, -) ≅ 𝓗om(A, -) ⊗ 𝓑_{b⁻¹}`, the identity on underlying sheaves. -/
noncomputable def ihomFunctorConstantTwistLeftIso (A : ProEtaleWeilSheaf k₀ l X)
    (b : (PadicAlgCl l)ˣ) :
    ihomFunctor k₀ l X ((constantTwist k₀ l X b).obj A) ≅
      ihomFunctor k₀ l X A ⋙ constantTwist k₀ l X b⁻¹ :=
  NatIso.ofComponents (fun B ↦ ihomConstantTwistLeftIso A B b) fun _ ↦ by
    apply IsoAlgebra.hom_ext
    simp [ihomConstantTwistLeftIso]
    rfl

/-- `𝓗om(A, - ⊗ 𝓑_c) ≅ 𝓗om(A, -) ⊗ 𝓑_c`, the identity on underlying sheaves. -/
noncomputable def constantTwistCompIhomFunctorIso (A : ProEtaleWeilSheaf k₀ l X)
    (c : (PadicAlgCl l)ˣ) :
    constantTwist k₀ l X c ⋙ ihomFunctor k₀ l X A ≅
      ihomFunctor k₀ l X A ⋙ constantTwist k₀ l X c :=
  NatIso.ofComponents (fun B ↦ ihomConstantTwistRightIso A B c) fun _ ↦ by
    apply IsoAlgebra.hom_ext
    simp [ihomConstantTwistRightIso]
    rfl

/-- `𝓗om(ℚ̄_ℓ(m)^∨, -)` is the constant twist by `χ_ℓ(σ)^m`. -/
noncomputable def ihomFunctorTateTwistIso (m : ℤ) :
    ihomFunctor k₀ l X ((WeilSheaf.tateTwistSheaf k₀ l X m).dual
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l X m)).obj ≅
      constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ m) :=
  ihomFunctorMapIsoLeft (WeilSheaf.dualObjIsoOfIso _ _
      (WeilSheaf.tateTwistSheafObjIso k₀ l X m)).symm ≪≫
    ihomFunctorConstantTwistLeftIso _ _ ≪≫
    Functor.isoWhiskerRight (ihomFunctorAdicConstantIso k₀ l X) _ ≪≫ Functor.leftUnitor _ ≪≫
    constantTwistFunctorCongrIso k₀ l X (inv_inv _)

/-- The derived internal hom `R𝓗om(ℚ̄_ℓ(m)^∨, -)` is the constant twist by `χ_ℓ(σ)^m`. -/
noncomputable def rightDerivedFunctorIhomFunctorTateTwistIso (m : ℤ) :
    (ihomFunctor k₀ l X ((WeilSheaf.tateTwistSheaf k₀ l X m).dual
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l X m)).obj).rightDerivedFunctor ≅
      (constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ m)).mapDerivedCategory :=
  Functor.rightDerivedFunctorNatIso (ihomFunctorTateTwistIso m) ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategory _

/-- The derived internal hom out of a pro-étale Weil sheaf commutes with constant twists. -/
noncomputable def mapDerivedCategoryConstantTwistCompRightDerivedIhomIso
    (A : ProEtaleWeilSheaf k₀ l X) (c : (PadicAlgCl l)ˣ) :
    (constantTwist k₀ l X c).mapDerivedCategory ⋙ (ihomFunctor k₀ l X A).rightDerivedFunctor ≅
      (ihomFunctor k₀ l X A).rightDerivedFunctor ⋙ (constantTwist k₀ l X c).mapDerivedCategory :=
  IsoAlgebra.mapDerivedCategoryTwistCompRightDerivedFunctorIso _ _ _
    (constantTwistCompIhomFunctorIso A c)

end Ihom

section UpperStar

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
  (b : (PadicAlgCl l)ˣ)

variable (k₀ l) in
/-- The pullback of pro-étale Weil sheaves commutes with constant twists. -/
noncomputable def constantTwistCompUpperStarIso :
    constantTwist k₀ l Y b ⋙ upperStar k₀ l φ ≅ upperStar k₀ l φ ⋙ constantTwist k₀ l X b :=
  constantTwistCompMapOfNatIsoIso k₀ l b (AdicSheaf.adicUpperStar_map_smul _)
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ _))

variable (k₀ l) in
/-- The derived pullback of pro-étale Weil sheaves commutes with constant twists. -/
noncomputable def mapDerivedCategoryConstantTwistCompUpperStarIso :
    (constantTwist k₀ l Y b).mapDerivedCategory ⋙ (upperStar k₀ l φ).mapDerivedCategory ≅
      (upperStar k₀ l φ).mapDerivedCategory ⋙ (constantTwist k₀ l X b).mapDerivedCategory :=
  IsoAlgebra.mapDerivedCategoryTwistCompMapDerivedCategoryIso _ _ _
    (constantTwistCompUpperStarIso k₀ l φ b)

end UpperStar

end ProEtaleWeilSheaf

end AlgebraicGeometry
