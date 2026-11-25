/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeHomSingle
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula

/-!
# Native tensor with the Tate sheaf

The native tensor and scalar Tate twist have the same right adjoint. The
comparison is therefore natural on the ambient derived category and restricts
to Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

/-- Two specified inverse functor isomorphisms give an adjunction. -/
noncomputable def CategoryTheory.Adjunction.ofInverseFunctorIsos
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (G : D ⥤ C)
    (e : F ⋙ G ≅ 𝟭 C) (e' : G ⋙ F ≅ 𝟭 D) : F ⊣ G :=
  (CategoryTheory.Equivalence.mk F G e.symm e').toAdjunction

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The scalar twist and inverse scalar twist induce a derived adjunction. -/
noncomputable def constantTwistDerivedAdjunction (b : (PadicAlgCl l)ˣ) :
    (constantTwist k₀ l X b).mapDerivedCategory ⊣
      (constantTwist k₀ l X b⁻¹).mapDerivedCategory := by
  let F := constantTwist k₀ l X b
  let G := constantTwist k₀ l X b⁻¹
  let ef : F ⋙ G ≅ 𝟭 _ :=
    constantTwistCompConstantTwistIso k₀ l X b b⁻¹ ≪≫
      constantTwistFunctorCongrIso k₀ l X (mul_inv_cancel b) ≪≫ constantTwistOneIso k₀ l X
  let eg : G ⋙ F ≅ 𝟭 _ :=
    constantTwistCompConstantTwistIso k₀ l X b⁻¹ b ≪≫
      constantTwistFunctorCongrIso k₀ l X (inv_mul_cancel b) ≪≫ constantTwistOneIso k₀ l X
  exact Adjunction.ofInverseFunctorIsos F.mapDerivedCategory G.mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso ef ≪≫ Functor.mapDerivedCategoryIdIso _)
    (Functor.mapDerivedCategoryCompIso G F ≪≫
      Functor.mapDerivedCategoryNatIso eg ≪≫ Functor.mapDerivedCategoryIdIso _)

/-- Internal Hom from the Tate sheaf is the inverse scalar twist. -/
noncomputable def ihomTateSheafIso (d : ℤ) :
    ihomFunctor k₀ l X (WeilSheaf.tateTwistSheaf k₀ l X d).obj ≅
      constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ d)⁻¹ :=
  ihomFunctorMapIsoLeft (WeilSheaf.tateTwistSheafObjIso k₀ l X d).symm ≪≫
    ihomFunctorConstantTwistLeftIso _ (WeilSheaf.cyclotomicUnit k₀ l ^ d) ≪≫
    Functor.isoWhiskerRight (ihomFunctorAdicConstantIso k₀ l X) _ ≪≫ Functor.leftUnitor _

/-- The native derived internal Hom from the Tate complex is the inverse twist. -/
noncomputable def nativeHomTateIso (d : ℤ) :
    Prod.sectR (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj
      (WeilSheaf.tateTwistSheaf k₀ l X d).obj)) _ ⋙
      (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      (constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ d)⁻¹).mapDerivedCategory :=
  nativeHomSingleIso _ ≪≫ Functor.rightDerivedFunctorNatIso (ihomTateSheafIso d) ≪≫
    (constantTwist k₀ l X
      (WeilSheaf.cyclotomicUnit k₀ l ^ d)⁻¹).rightDerivedFunctorIsoMapDerivedCategory

/-- The tensor functor of the native closed model in fixed-source coordinates. -/
noncomputable def nativeTensorRightSectRIso
    (T : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    letI := (nativeDerivedClosedComparison k₀ l X).weilClosed.monoidal
    tensorRight T ≅ Prod.sectR T _ ⋙ nativeDerivedTensor k₀ l X := by
  let C := nativeDerivedClosedComparison k₀ l X
  letI := C.weilClosed.monoidal
  letI := C.weilSymmetry
  exact (BraidedCategory.tensorLeftIsoTensorRight T).symm ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
      dsimp [nativeDerivedTensor, WeilConjectures.CoefficientClosedStructure.tensor]
      change T ◁ g ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 T ⊗ₘ g)
      simp)

/-- Native derived tensor with the Tate sheaf is the derived scalar twist. -/
noncomputable def nativeDerivedTensorTateIso (d : ℤ) :
    Prod.sectR ((DerivedCategory.singleFunctor _ 0).obj
      (WeilSheaf.tateTwistSheaf k₀ l X d).obj) _ ⋙ nativeDerivedTensor k₀ l X ≅
      (constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ d)).mapDerivedCategory := by
  let C := nativeDerivedClosedComparison k₀ l X
  letI := C.weilClosed.monoidal
  let T := (DerivedCategory.singleFunctor _ 0).obj (WeilSheaf.tateTwistSheaf k₀ l X d).obj
  exact (nativeTensorRightSectRIso T).symm ≪≫
    ((C.weilClosed.adjunction T).ofNatIsoRight (nativeHomTateIso d)).leftAdjointUniq
      (constantTwistDerivedAdjunction (WeilSheaf.cyclotomicUnit k₀ l ^ d))

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The native tensor by a Tate sheaf agrees with the existing Tate twist functor. -/
noncomputable def nativeConstructibleTensorTateIso (d : ℤ) :
    Prod.sectR (WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k₀ l X d)) _ ⋙
      nativeConstructibleTensor k₀ l X ≅ tateTwist k₀ l X d :=
  ((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (objectProperty k₀ l X).ι
      (ProEtaleWeilSheaf.nativeDerivedTensorTateIso d) ≪≫ (tateTwistCompιIso d).symm)

end AlgebraicGeometry.WeilComplex
