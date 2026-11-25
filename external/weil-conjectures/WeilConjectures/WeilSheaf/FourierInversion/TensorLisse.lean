/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist
public import WeilConjectures.WeilSheaf.IhomLisse.CompWeil
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Fourier inversion: tensor products with lisse sheaves and direct images

Formal properties of the tensor product with a lisse Weil sheaf, the Tate twist, and the
compact-support direct image along proper morphisms and the identity.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section TensorLisse

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- An isomorphism of lisse Weil sheaves induces an isomorphism of their duals. -/
noncomputable def WeilSheaf.dualIsoOfIso {G G' : WeilSheaf k₀ l X} (e : G ≅ G') (hG : G.IsLisse)
    (hG' : G'.IsLisse) : G.dual hG ≅ G'.dual hG' :=
  ObjectProperty.isoMk _ (ProEtaleWeilSheaf.ihomMapIsoLeft ((ObjectProperty.ι _).mapIso e).symm _)

/-- The dual of the constant Weil sheaf `ℚ̄_ℓ` is `ℚ̄_ℓ`. -/
noncomputable def WeilSheaf.dualAdicConstantIso :
    (WeilSheaf.adicConstant k₀ l X).dual (WeilSheaf.isLisse_adicConstant k₀ l X) ≅
      WeilSheaf.adicConstant k₀ l X :=
  ObjectProperty.isoMk _ (ProEtaleWeilSheaf.ihomAdicConstantIso _)

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The derived internal hom out of a lisse Weil sheaf followed by the inclusion into the derived
category is the inclusion followed by the right derived functor of the internal hom. -/
noncomputable def WeilComplex.ihomLisseCompιIso (F : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    WeilComplex.ihomLisse F hF ⋙ (WeilComplex.objectProperty k₀ l X).ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙
        (ProEtaleWeilSheaf.ihomFunctor k₀ l X F.obj).rightDerivedFunctor :=
  ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- The derived internal hom out of a lisse Weil sheaf only depends on the sheaf up to
isomorphism. -/
noncomputable def WeilComplex.ihomLisseIsoOfIso {F F' : WeilSheaf k₀ l X} (e : F ≅ F')
    (hF : F.IsLisse) (hF' : F'.IsLisse) :
    WeilComplex.ihomLisse F hF ≅ WeilComplex.ihomLisse F' hF' :=
  ((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (WeilComplex.ihomLisseCompιIso F hF ≪≫
      Functor.isoWhiskerLeft (WeilComplex.objectProperty k₀ l X).ι
        (Functor.rightDerivedFunctorNatIso
          (ProEtaleWeilSheaf.ihomFunctorMapIsoLeft ((ObjectProperty.ι _).mapIso e.symm))) ≪≫
      (WeilComplex.ihomLisseCompιIso F' hF').symm)

/-- The derived internal hom out of the constant Weil sheaf `ℚ̄_ℓ` is the identity. -/
noncomputable def WeilComplex.ihomLisseAdicConstantIso :
    WeilComplex.ihomLisse (WeilSheaf.adicConstant k₀ l X)
        (WeilSheaf.isLisse_adicConstant k₀ l X) ≅ 𝟭 _ :=
  ((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (WeilComplex.ihomLisseCompιIso _ _ ≪≫
      Functor.isoWhiskerLeft (WeilComplex.objectProperty k₀ l X).ι
        (Functor.rightDerivedFunctorNatIso
          (ProEtaleWeilSheaf.ihomFunctorAdicConstantIso k₀ l X) ≪≫
        Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The tensor product with a lisse Weil sheaf only depends on the sheaf up to isomorphism. -/
theorem WeilComplex.nonempty_iso_tensorLisse_of_iso {G G' : WeilSheaf k₀ l X} (e : G ≅ G')
    (hG : G.IsLisse) (hG' : G'.IsLisse) :
    Nonempty (WeilComplex.tensorLisse G hG ≅ WeilComplex.tensorLisse G' hG') :=
  ⟨WeilComplex.ihomLisseIsoOfIso (WeilSheaf.dualIsoOfIso e hG hG') _ _⟩

/-- Internal homs out of the duals of two lisse Weil sheaves compose to the internal hom out of
the dual of their tensor product: `[G^∨, [H^∨, -]] ≅ [(G ⊗ H)^∨, -]`. -/
noncomputable def ProEtaleWeilSheaf.ihomFunctorDualCompIhomFunctorDualIso (G H : WeilSheaf k₀ l X)
    (hG : G.IsLisse) (hH : H.IsLisse) :
    ProEtaleWeilSheaf.ihomFunctor k₀ l X (H.dual hH).obj ⋙
        ProEtaleWeilSheaf.ihomFunctor k₀ l X (G.dual hG).obj ≅
      ProEtaleWeilSheaf.ihomFunctor k₀ l X
        ((G.tensorObj H hG).dual (ProEtale.IsAdicLisseSheaf.ihom hG.dual hH)).obj :=
  (ProEtaleWeilSheaf.ihomFunctorIsoIhomFunctorCompIhomFunctor (G.dual hG).obj H.obj
    (ProEtaleWeilSheaf.adicConstant k₀ l X) hG.dual).symm

/-- Tensoring successively with two lisse Weil sheaves is tensoring with their tensor
product: `G ⊗ (H ⊗ K) ≅ (G ⊗ H) ⊗ K`. -/
theorem WeilComplex.nonempty_iso_tensorLisse_comp (G H : WeilSheaf k₀ l X) (hG : G.IsLisse)
    (hH : H.IsLisse) :
    Nonempty (WeilComplex.tensorLisse H hH ⋙ WeilComplex.tensorLisse G hG ≅
      WeilComplex.tensorLisse (G.tensorObj H hG) (ProEtale.IsAdicLisseSheaf.ihom hG.dual hH)) := by
  unfold WeilComplex.tensorLisse
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (G.dual hG).obj hG.dual
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (H.dual hH).obj hH.dual
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor
    ((G.tensorObj H hG).dual (ProEtale.IsAdicLisseSheaf.ihom hG.dual hH)).obj
    (WeilSheaf.IsLisse.dual (F := G.tensorObj H hG) (ProEtale.IsAdicLisseSheaf.ihom hG.dual hH))
  exact ⟨((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (WeilComplex.ihomLisseCompιIso _ hG.dual) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (WeilComplex.ihomLisseCompιIso _ hH.dual) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory _) _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorIsoMapDerivedCategory _) ≪≫
          Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso
            (ProEtaleWeilSheaf.ihomFunctorDualCompIhomFunctorDualIso G H hG hH) ≪≫
          (Functor.rightDerivedFunctorIsoMapDerivedCategory _).symm) ≪≫
      (WeilComplex.ihomLisseCompιIso _ _).symm)⟩

/-- Tensoring with the constant Weil sheaf `ℚ̄_ℓ` is the identity. -/
theorem WeilComplex.nonempty_iso_tensorLisse_adicConstant :
    Nonempty (WeilComplex.tensorLisse (WeilSheaf.adicConstant k₀ l X)
      (WeilSheaf.isLisse_adicConstant k₀ l X) ≅ 𝟭 _) :=
  ⟨WeilComplex.ihomLisseIsoOfIso WeilSheaf.dualAdicConstantIso _ _ ≪≫
    WeilComplex.ihomLisseAdicConstantIso⟩

variable (k₀ l X) in
/-- Twisting pro-étale Weil sheaves by `b` and then by `c` is twisting by `b * c`. -/
noncomputable def ProEtaleWeilSheaf.constantTwistCompConstantTwistIso (b c : (PadicAlgCl l)ˣ) :
    ProEtaleWeilSheaf.constantTwist k₀ l X b ⋙ ProEtaleWeilSheaf.constantTwist k₀ l X c ≅
      ProEtaleWeilSheaf.constantTwist k₀ l X (b * c) :=
  NatIso.ofComponents (ProEtaleWeilSheaf.constantTwistObjConstantTwistIso b c) fun _ ↦
    IsoAlgebra.hom_ext ((Category.comp_id _).trans (Category.id_comp _).symm)

variable (k₀ l X) in
/-- Twisting pro-étale Weil sheaves by `1` is the identity. -/
noncomputable def ProEtaleWeilSheaf.constantTwistOneIso :
    ProEtaleWeilSheaf.constantTwist k₀ l X 1 ≅ 𝟭 _ :=
  NatIso.ofComponents ProEtaleWeilSheaf.constantTwistOneObjIso fun _ ↦
    IsoAlgebra.hom_ext ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The Tate twist followed by the inclusion into the derived category is the inclusion
followed by the constant twist by `χ_ℓ(σ)^m`. -/
noncomputable def WeilComplex.tateTwistCompιIso (m : ℤ) :
    WeilComplex.tateTwist k₀ l X m ⋙ (WeilComplex.objectProperty k₀ l X).ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙ (ProEtaleWeilSheaf.constantTwist k₀ l X
        (WeilSheaf.cyclotomicUnit k₀ l ^ m)).mapDerivedCategory :=
  WeilComplex.ihomLisseCompιIso _ (WeilSheaf.isLisse_tateTwistSheaf k₀ l X m).dual ≪≫
    Functor.isoWhiskerLeft (WeilComplex.objectProperty k₀ l X).ι
      (ProEtaleWeilSheaf.rightDerivedFunctorIhomFunctorTateTwistIso m)

/-- The Tate twists by `m` and `n` with `m + n = 0` compose to the identity. -/
noncomputable def WeilComplex.tateTwistCompTateTwistIso (m n : ℤ) (h : m + n = 0) :
    WeilComplex.tateTwist k₀ l X m ⋙ WeilComplex.tateTwist k₀ l X n ≅ 𝟭 _ :=
  ((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (WeilComplex.tateTwistCompιIso n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (WeilComplex.tateTwistCompιIso m) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtaleWeilSheaf.constantTwistCompConstantTwistIso k₀ l X _ _ ≪≫
            ProEtaleWeilSheaf.constantTwistFunctorCongrIso k₀ l X
              (by rw [← zpow_add, h, zpow_zero]) ≪≫
            ProEtaleWeilSheaf.constantTwistOneIso k₀ l X) ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The Tate twist of Weil complexes is an autoequivalence (its quasi-inverse is the Tate
twist by the opposite integer). -/
theorem WeilComplex.isEquivalence_tateTwist (m : ℤ) :
    (WeilComplex.tateTwist k₀ l X m).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (WeilComplex.tateTwist k₀ l X m)
    (WeilComplex.tateTwist k₀ l X (-m))
    (WeilComplex.tateTwistCompTateTwistIso m (-m) (add_neg_cancel m)).symm
    (WeilComplex.tateTwistCompTateTwistIso (-m) m (neg_add_cancel m))).isEquivalence_functor

variable (k₀ l X) in
/-- For `m + n = 0` and `a + b = 0`, the twist-shift `K ↦ K(m)[a]` followed by `K ↦ K(n)[b]` is the
identity. -/
noncomputable def WeilComplex.tateTwistShiftCompTateTwistShiftIso (m n a b : ℤ) (hmn : m + n = 0)
    (hab : a + b = 0) :
    (WeilComplex.tateTwist k₀ l X m ⋙ shiftFunctor (WeilComplex k₀ l X) a) ⋙
        (WeilComplex.tateTwist k₀ l X n ⋙ shiftFunctor (WeilComplex k₀ l X) b) ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft (WeilComplex.tateTwist k₀ l X m)
      (Functor.isoWhiskerRight ((WeilComplex.tateTwist k₀ l X n).commShiftIso a)
        (shiftFunctor (WeilComplex k₀ l X) b)) ≪≫
    Functor.isoWhiskerLeft (WeilComplex.tateTwist k₀ l X m ⋙ WeilComplex.tateTwist k₀ l X n)
      (shiftFunctorCompIsoId (WeilComplex k₀ l X) a b hab) ≪≫
    Functor.rightUnitor _ ≪≫ WeilComplex.tateTwistCompTateTwistIso m n hmn

variable (k₀ l X) in
/-- For `m + n = 0` and `a + b = 0`, the twist-shifts `K ↦ K(m)[a]` and `K ↦ K(n)[b]` are inverse
autoequivalences of the Weil complexes. -/
noncomputable def WeilComplex.tateTwistShiftEquiv (m n a b : ℤ) (hmn : m + n = 0)
    (hab : a + b = 0) : WeilComplex k₀ l X ≌ WeilComplex k₀ l X :=
  CategoryTheory.Equivalence.mk
    (WeilComplex.tateTwist k₀ l X m ⋙ shiftFunctor (WeilComplex k₀ l X) a)
    (WeilComplex.tateTwist k₀ l X n ⋙ shiftFunctor (WeilComplex k₀ l X) b)
    (WeilComplex.tateTwistShiftCompTateTwistShiftIso k₀ l X m n a b hmn hab).symm
    (WeilComplex.tateTwistShiftCompTateTwistShiftIso k₀ l X n m b a (by omega) (by omega))

end TensorLisse

attribute [local instance] Compactification.over

/-- For a proper morphism the compact-support direct image of Weil complexes is the direct
image, `Rf₀! ≅ Rf₀*` (the open immersion of the chosen compactification is then also closed;
compare `AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoOfIsProper`). -/
theorem WeilComplex.nonempty_iso_derivedLowerShriek_derivedLowerStar {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l f ≅ WeilComplex.derivedLowerStar f) := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have : IsProper c.i := c.isProper_openImmersion inferInstance
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  exact ⟨((WeilComplex.objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (WeilComplex.objectProperty k₀ l X).ι
      (Functor.isoWhiskerRight
          (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.symm
          (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor ≪≫
        (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
          (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
            (comp_over c.i _))
          (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g
            (comp_over c.g _))).symm ≪≫
        Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
          (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
          (ProEtaleWeilSheaf.lowerStar k₀ l c.g)) ≪≫
        Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g) ≪≫
        Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)))⟩

/-- The derived direct image of Weil complexes along the identity is the identity. -/
noncomputable def WeilComplex.derivedLowerStarIdIso {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    (WeilComplex.derivedLowerStar (𝟙 X) : WeilComplex k₀ l X ⥤ WeilComplex k₀ l X) ≅ 𝟭 _ :=
  ((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (WeilComplex.objectProperty k₀ l X).ι
        (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarIdIso k₀ l X) ≪≫
          Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
          Functor.mapDerivedCategoryIdIso _) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The compact-support direct image along the identity is the identity. -/
theorem WeilComplex.nonempty_iso_derivedLowerShriek_id {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l (𝟙 X) ≅ 𝟭 _) :=
  (WeilComplex.nonempty_iso_derivedLowerShriek_derivedLowerStar (𝟙 X)).map
    (· ≪≫ WeilComplex.derivedLowerStarIdIso)

end AlgebraicGeometry
