/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.Native.NativeHomSingle
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist

/-!
# Tate twists as tensor products of Weil complexes

The Tate twist `K ↦ K(m)` of Weil complexes (`AlgebraicGeometry.WeilComplex.tateTwist`) is
defined as the derived tensor product with the lisse Tate sheaf `ℚ̄_ℓ(m)`, through the derived
internal hom out of its dual. This file compares it, followed by a shift `[n]`, with the native
derived tensor product of Weil complexes
(`AlgebraicGeometry.WeilComplex.nativeConstructibleTensor`) with the Weil complex `ℚ̄_ℓ(m)[n]`
(`AlgebraicGeometry.WeilComplex.nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift`).

## Proof

Put `b = χ_ℓ(σ)ᵐ`, so that `ℚ̄_ℓ(m)` is the constant twist `ℚ̄_ℓ ⊗ 𝓑_b` and the Tate twist is the
derived constant twist `T_b` by `b` (`AlgebraicGeometry.WeilComplex.tateTwistCompιIso`). The
native tensor product `- ⊗ B` with `B = ℚ̄_ℓ(m)[n]` is left adjoint to the native internal hom
`RHom(B, -)`. As `B` is the sheaf `ℚ̄_ℓ ⊗ 𝓑_b` placed in degree `-n`, this internal hom is
`R𝓗om(ℚ̄_ℓ ⊗ 𝓑_b, -)[-n] = T_{b⁻¹}(-)[-n]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilHomSingleIso`), the inverse of the equivalence
`T_b(-)[n]`. Hence `- ⊗ B ≅ T_b(-)[n]`, by uniqueness of left adjoints.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.WeilComplex

open ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The Tate sheaf `ℚ̄_ℓ(m)`, as the Tate twist of the Weil complex `ℚ̄_ℓ`, is the constant twist
`ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ}` placed in degree `0`. -/
noncomputable def tateTwistObjAdicConstantIso (m : ℤ) :
    ((tateTwist k₀ l X m).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X))).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ m)).obj (adicConstant k₀ l X)) :=
  (tateTwistCompιIso (k₀ := k₀) (l := l) (X := X) m).app _ ≪≫
    ((constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ m)).mapDerivedCategorySingleFunctor
      0).app (adicConstant k₀ l X)

/-- The shifted Tate sheaf `ℚ̄_ℓ(m)[n]` is the constant twist `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ}` placed in
degree `-n`. -/
noncomputable def tateTwistShiftObjIso (m n : ℤ) :
    (((tateTwist k₀ l X m).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦n⟧).obj ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ (-n)).obj
        ((constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ m)).obj
          (adicConstant k₀ l X))) :=
  ((objectProperty k₀ l X).ι.commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso (tateTwistObjAdicConstantIso k₀ l X m) ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by omega)).app _

/-- The native internal hom out of the shifted Tate sheaf `ℚ̄_ℓ(m)[n]` is the derived constant
twist by `χ_ℓ(σ)⁻ᵐ`, followed by the shift `[-n]`. -/
noncomputable def nativeWeilHomTateTwistShiftIso (m n : ℤ) :
    Prod.sectR (op (((tateTwist k₀ l X m).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦n⟧).obj)
        (DerivedCategory (ProEtaleWeilSheaf k₀ l X)) ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      (constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ m)⁻¹).mapDerivedCategory ⋙
        shiftFunctor _ (-n) :=
  Functor.isoWhiskerRight (NatIso.ofComponents
      (fun Z ↦ Iso.prod (tateTwistShiftObjIso k₀ l X m n).symm.op (Iso.refl Z))
      (fun f ↦ by
        ext
        · simp only [Prod.sectR_map, prod_comp, Iso.prod_hom]
          erw [Category.id_comp, Category.comp_id]
        · simp only [Prod.sectR_map, prod_comp, Iso.prod_hom]
          erw [Category.id_comp, Category.comp_id])) _ ≪≫
    nativeWeilHomSingleIso _ (-n) ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorNatIso
        (ihomFunctorConstantTwistLeftIso _ _ ≪≫
          Functor.isoWhiskerRight (ihomFunctorAdicConstantIso k₀ l X) _ ≪≫ Functor.leftUnitor _) ≪≫
      Functor.rightDerivedFunctorIsoMapDerivedCategory _) _

/-- The derived constant twist by `χ_ℓ(σ)ᵐ` followed by the shift `[n]` is left adjoint to the
derived constant twist by `χ_ℓ(σ)⁻ᵐ` followed by the shift `[-n]`: both are equivalences, inverse
to each other. -/
noncomputable def constantTwistShiftAdjunction (b : (PadicAlgCl l)ˣ) (n : ℤ) :
    (constantTwist k₀ l X b).mapDerivedCategory ⋙ shiftFunctor _ n ⊣
      (constantTwist k₀ l X b⁻¹).mapDerivedCategory ⋙ shiftFunctor _ (-n) :=
  haveI : (Endofunctor.IsoAlgebra.twistEquivalence
      (frobeniusPullbackSmulIso k₀ l X b)).functor.Additive :=
    inferInstanceAs (Endofunctor.IsoAlgebra.twist _).Additive
  haveI : (Endofunctor.IsoAlgebra.twistEquivalence
      (frobeniusPullbackSmulIso k₀ l X b)).inverse.Additive :=
    inferInstanceAs (Endofunctor.IsoAlgebra.twist _).Additive
  (((Endofunctor.IsoAlgebra.twistEquivalence
      (frobeniusPullbackSmulIso k₀ l X b)).mapDerivedCategory.trans
        (shiftEquiv (DerivedCategory (ProEtaleWeilSheaf k₀ l X)) n)).toAdjunction).ofNatIsoRight
    (Functor.isoWhiskerLeft (shiftFunctor _ (-n)) (Functor.mapDerivedCategoryNatIso
        (NatIso.ofComponents (fun K ↦ Endofunctor.IsoAlgebra.isoMk (Iso.refl _) (by simp))
          (fun f ↦ Endofunctor.IsoAlgebra.hom_ext
            ((Category.comp_id _).trans (Category.id_comp _).symm)))) ≪≫
      (constantTwist k₀ l X b⁻¹).mapDerivedCategory.commShiftIso (-n))

/-- **Tate twists are tensor products** (blueprint: `definition-tate-twists`, where the Tate twist
`K(m) = K ⊗^L ℚ̄_ℓ(m)` is the derived tensor product with the Tate sheaf): for a Weil complex `K`
on `X`, the native derived tensor product `K ⊗ ℚ̄_ℓ(m)[n]` is the shifted Tate twist `K(m)[n]`,
naturally in `K`.

Both functors are left adjoint to `T_{b⁻¹}(-)[-n]`, `b = χ_ℓ(σ)ᵐ`: the native tensor product by
the tensor–hom adjunction and the computation of the internal hom out of `ℚ̄_ℓ(m)[n]`
(`AlgebraicGeometry.WeilComplex.nativeWeilHomTateTwistShiftIso`), and the Tate twist since it is
the derived constant twist `T_b` (`AlgebraicGeometry.WeilComplex.tateTwistCompιIso`). -/
theorem nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift (m n : ℤ) :
    Nonempty ((𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const (WeilComplex k₀ l X)).obj
        (((tateTwist k₀ l X m).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦n⟧)) ⋙
          nativeConstructibleTensor k₀ l X ≅
      tateTwist k₀ l X m ⋙ shiftFunctor (WeilComplex k₀ l X) n) := by
  let := (nativeDerivedClosedComparison k₀ l X).weilClosed.monoidal
  let B := ((tateTwist k₀ l X m).obj
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦n⟧
  let ι := (objectProperty k₀ l X).ι
  -- `- ⊗ B ≅ T_b(-)[n]` on the derived category, by uniqueness of left adjoints
  let u : MonoidalCategory.tensorRight B.obj ≅
      (constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ m)).mapDerivedCategory ⋙
        shiftFunctor _ n :=
    ((nativeDerivedClosedComparison k₀ l X).weilClosed.adjunction B.obj).leftAdjointUniq
      ((constantTwistShiftAdjunction k₀ l X _ n).ofNatIsoRight
        (nativeWeilHomTateTwistShiftIso k₀ l X m n).symm)
  let e : ((𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const (WeilComplex k₀ l X)).obj B) ⋙
        nativeConstructibleTensor k₀ l X) ⋙ ι ≅
      (tateTwist k₀ l X m ⋙ shiftFunctor (WeilComplex k₀ l X) n) ⋙ ι :=
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
        dsimp [nativeConstructibleTensor, nativeDerivedTensor,
          WeilConjectures.CoefficientClosedStructure.tensor, ι]
        simp only [Category.comp_id, Category.id_comp]
        exact MonoidalCategory.tensorHom_id f.hom B.obj) :
        ((𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const (WeilComplex k₀ l X)).obj B) ⋙
          nativeConstructibleTensor k₀ l X) ⋙ ι ≅ ι ⋙ MonoidalCategory.tensorRight B.obj) ≪≫
      Functor.isoWhiskerLeft ι u ≪≫
      Functor.isoWhiskerRight (tateTwistCompιIso (k₀ := k₀) (l := l) (X := X) m).symm _ ≪≫
      Functor.isoWhiskerLeft (tateTwist k₀ l X m) (ι.commShiftIso n).symm
  exact ⟨((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso e⟩

end AlgebraicGeometry.WeilComplex
