/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Tensor

/-!
# Cohomology of constant Weil twists

For a unit `b ∈ ℚ̄_ℓˣ`, the constant Weil twist `F ⊗ 𝓑_b` of a Weil sheaf `F`
(`AlgebraicGeometry.WeilSheaf.constantTwist`) has the underlying sheaf of `F` and the Weil
structure `b • φ`. Multiplication by `b` is an automorphism of the Frobenius pullback, and the
constant twist is the twist of pro-étale Weil sheaves by it
(`AlgebraicGeometry.ProEtaleWeilSheaf.constantTwist`, an instance of
`CategoryTheory.Endofunctor.IsoAlgebra.twist`). Pushforwards are `ℚ̄_ℓ`-linear, so they commute
with constant twists, and so do their right derived functors. Hence the cohomology of
`F ⊗ 𝓑_b` is that of `F`, with the geometric Frobenius multiplied by `b`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_cohomology_constantTwist`:
  `Hʳ(X ⊗ k̄, F ⊗ 𝓑_b) ≅ Hʳ(X ⊗ k̄, F)` with the Frobenius multiplied by `b`.
- `AlgebraicGeometry.WeilSheaf.nonempty_higherLowerShriek_constantTwist_iso`:
  `Rⁱf₀!(F ⊗ 𝓑_b) ≅ Rⁱf₀!F ⊗ 𝓑_b` (blueprint: `proposition-purity-lisse-part-fourier-transform`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor


namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {Z₁ Z₂ : Scheme.{u}}

/-- A left adjoint of a functor commuting with multiplication by scalars commutes with it. -/
lemma map_smul_of_adjunction {L : AdicSheaf l Z₁ ⥤ AdicSheaf l Z₂}
    {R : AdicSheaf l Z₂ ⥤ AdicSheaf l Z₁} (adj : L ⊣ R)
    (hR : ∀ c M, R.map (smul c M) = smul c (R.obj M)) (c : ULift.{u + 1} (PadicAlgCl l))
    (M : AdicSheaf l Z₁) : L.map (smul c M) = smul c (L.obj M) :=
  (adj.homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, adj.unit_naturality, hR]
    exact smul_comp _ _)

/-- The pullback commutes with multiplication by a scalar. -/
lemma adicUpperStar_map_smul (g : Z₁ ⟶ Z₂) (c : ULift.{u + 1} (PadicAlgCl l))
    (M : AdicSheaf l Z₂) : (g)^*ᵃ[l].map (smul c M) = smul c ((g)^*ᵃ[l].obj M) :=
  map_smul_of_adjunction (adicUpperStarLowerStarAdjunction l g) (adicLowerStar_map_smul g) c M

/-- The extension by zero along an open immersion commutes with multiplication by a scalar. -/
lemma adicOpenImmersionLowerShriek_map_smul (j : Z₁ ⟶ Z₂) [IsOpenImmersion j]
    (c : ULift.{u + 1} (PadicAlgCl l)) (M : AdicSheaf l Z₁) :
    (j)_!ᵃ[l].map (smul c M) = smul c ((j)_!ᵃ[l].obj M) :=
  map_smul_of_adjunction (adicOpenImmersionLowerShriekAdjunction l j)
    (adicUpperStar_map_smul j) c M

end AlgebraicGeometry.ProEtale.AdicSheaf

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Multiplication by a unit `b ∈ ℚ̄_ℓˣ`, as an automorphism of the Frobenius pullback. -/
noncomputable def frobeniusPullbackSmulIso (b : (PadicAlgCl l)ˣ) :
    WeilSheaf.frobeniusPullback k₀ l X ≅ WeilSheaf.frobeniusPullback k₀ l X :=
  NatIso.ofComponents (fun _ ↦ WeilCoefficients.smulIso b _) fun _ ↦
    (AdicSheaf.smul_comp _ _).symm

@[simp]
lemma frobeniusPullbackSmulIso_hom_app (b : (PadicAlgCl l)ˣ)
    (M : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (frobeniusPullbackSmulIso k₀ l X b).hom.app M =
      AdicSheaf.smul (ULift.up (b : PadicAlgCl l)) _ :=
  rfl

/-- The constant Weil twist of pro-étale Weil sheaves by a unit `b ∈ ℚ̄_ℓˣ`: the underlying
sheaf is unchanged and the Weil structure `φ` becomes `b • φ`. -/
noncomputable abbrev constantTwist (b : (PadicAlgCl l)ˣ) :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.twist (frobeniusPullbackSmulIso k₀ l X b)

/-- A pro-étale Weil sheaf whose Weil structure is multiplied by `b` is its constant twist. -/
noncomputable def mkConstantTwistIso (K : ProEtaleWeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    IsoAlgebra.mk K.carrier (K.str ≪≫ WeilCoefficients.smulIso b K.carrier) ≅
      (constantTwist k₀ l X b).obj K :=
  IsoAlgebra.isoMk (Iso.refl _) (by
    dsimp only [constantTwist]
    rw [IsoAlgebra.twist_obj_obj_str]
    change (WeilSheaf.frobeniusPullback k₀ l X).map (𝟙 K.carrier) ≫
        AdicSheaf.smul _ ((WeilSheaf.frobeniusPullback k₀ l X).obj K.carrier) ≫ K.obj.str =
      (K.obj.str ≫ AdicSheaf.smul _ K.carrier) ≫ 𝟙 K.carrier
    have key {a : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
        (s : (WeilSheaf.frobeniusPullback k₀ l X).obj a ⟶ a) :
        (WeilSheaf.frobeniusPullback k₀ l X).map (𝟙 a) ≫
          AdicSheaf.smul (ULift.up (b : PadicAlgCl l))
            ((WeilSheaf.frobeniusPullback k₀ l X).obj a) ≫ s =
        (s ≫ AdicSheaf.smul (ULift.up (b : PadicAlgCl l)) a) ≫ 𝟙 a := by
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      exact AdicSheaf.smul_comp _ _
    exact key _)

end ProEtaleWeilSheaf

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The constant Weil twist of a Weil sheaf is the constant twist of its underlying pro-étale
Weil sheaf. -/
noncomputable def constantTwistObjIso (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    (F.constantTwist b).obj ≅ (ProEtaleWeilSheaf.constantTwist k₀ l X b).obj F.obj :=
  ProEtaleWeilSheaf.mkConstantTwistIso k₀ l X F.obj b

end WeilSheaf

end AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The underlying morphism of global sections of a morphism of Weil sheaves. -/
noncomputable abbrev globalSectionsMap {G G' : WeilSheaf k₀ l X} (f : G ⟶ G') :
    (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj G.obj.carrier.X ⟶
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj G'.obj.carrier.X :=
  (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map f.hom.hom.f)

/-- The Frobenius of global sections, as a morphism of `ℚ̄_ℓ`-modules. -/
noncomputable abbrev globalSectionsFrobeniusHom (G : WeilSheaf k₀ l X) :
    (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj G.obj.carrier.X ⟶
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj G.obj.carrier.X :=
  ((ProEtale.globalSectionsLowerStarIso _
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).app G.obj.carrier.X).inv ≫
    (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map G.obj.str.hom)

omit [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
lemma globalSectionsMap_comp_frobeniusHom {G G' : WeilSheaf k₀ l X} (f : G ⟶ G') :
    globalSectionsMap f ≫ globalSectionsFrobeniusHom G' =
      globalSectionsFrobeniusHom G ≫ globalSectionsMap f := by
  have h₁ := ((ProEtale.globalSectionsLowerStarIso _
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.naturality
    ((AdicSheaf.forget _).map f.hom.hom.f))
  have h₂ := congrArg (fun g ↦ (Sheaf.Γ _ (WeilCoefficients.{u} l)).map
    ((AdicSheaf.forget _).map g)) f.hom.hom.h
  simp only [Functor.map_comp] at h₂
  simp only [globalSectionsMap, globalSectionsFrobeniusHom, Category.assoc, Iso.app_inv]
  erw [reassoc_of% h₁]
  exact congrArg (_ ≫ ·) h₂

/-- Isomorphic Weil sheaves have isomorphic global sections, with their Frobenius. -/
noncomputable def globalSectionsEquivOfIso {G G' : WeilSheaf k₀ l X} (e : G ≅ G') :
    G.globalSections.Equiv G'.globalSections where
  toLinearEquiv := WeilCoefficients.linearEquivOfIso
    ((Sheaf.Γ _ _).mapIso ((AdicSheaf.forget _).mapIso
      ((IsoAlgebra.forget _).mapIso ((ObjectProperty.ι _).mapIso e))))
  map_frobenius x := by
    have h := congrArg (fun g ↦ ((WeilCoefficients.toModuleCat l).map g).hom x)
      (globalSectionsMap_comp_frobeniusHom e.hom)
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.symm

omit [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
lemma globalSectionsFrobeniusHom_constantTwist (G : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    globalSectionsFrobeniusHom (G.constantTwist b) =
      globalSectionsFrobeniusHom G ≫ ((ULift.up (b : PadicAlgCl l)) • 𝟙 _) := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)).Linear (ULift.{u + 1} (PadicAlgCl l)) :=
    (constantSheafΓAdj _ _).right_adjoint_linear
  have key {a : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)} {a' : Sheaf (Scheme.ProEt.topology
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (WeilCoefficients.{u} l)} (s : a' ⟶ a) :
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).map (s ≫ ((ULift.up (b : PadicAlgCl l)) • 𝟙 a)) =
        (Sheaf.Γ _ _).map s ≫ ((ULift.up (b : PadicAlgCl l)) • 𝟙 _) := by
    rw [Functor.map_comp, Functor.map_smul, CategoryTheory.Functor.map_id]
  exact (congrArg (_ ≫ ·) (key _)).trans (Category.assoc _ _ _).symm

/-- The global sections of a constant twist `G ⊗ 𝓑_b` are those of `G`, with the Frobenius
multiplied by `b`. -/
noncomputable def globalSectionsConstantTwistEquiv (G : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    (G.constantTwist b).globalSections.Equiv (G.globalSections.rescale b) where
  toLinearEquiv := LinearEquiv.refl _ _
  map_frobenius x := by
    change ((WeilCoefficients.toModuleCat l).map
      (globalSectionsFrobeniusHom (G.constantTwist b))).hom x =
        (G.globalSections.rescale b).frobenius x
    rw [globalSectionsFrobeniusHom_constantTwist]
    exact (FrobeniusModule.frobeniusEnd_rescale_apply (M := G.globalSections)
      (Units.ne_zero b) x).symm

end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry

open ProEtale
open scoped ProEtale

namespace ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] (b : (PadicAlgCl l)ˣ)

/-- A functor commuting with multiplication by scalars commutes with it compatibly with any
transport isomorphism `e : L ⋙ F₂ ≅ F₁ ⋙ L`. -/
lemma smul_comp_hom_app {Z₁ Z₂ : Scheme.{u}} {L : AdicSheaf l Z₁ ⥤ AdicSheaf l Z₂}
    (hL : ∀ c M, L.map (AdicSheaf.smul c M) = AdicSheaf.smul c (L.obj M))
    {F₁ : AdicSheaf l Z₁ ⥤ AdicSheaf l Z₁} {F₂ : AdicSheaf l Z₂ ⥤ AdicSheaf l Z₂}
    (e : L ⋙ F₂ ≅ F₁ ⋙ L) (c : ULift.{u + 1} (PadicAlgCl l)) (a : AdicSheaf l Z₁) :
    AdicSheaf.smul c (F₂.obj (L.obj a)) ≫ e.hom.app a =
      e.hom.app a ≫ L.map (AdicSheaf.smul c (F₁.obj a)) := by
  rw [hL]
  exact AdicSheaf.smul_comp _ _

variable (k₀ l) in
/-- The pushforward of pro-étale Weil sheaves commutes with constant twists. -/
noncomputable def constantTwistCompLowerStarIso :
    constantTwist k₀ l X b ⋙ lowerStar k₀ l φ ≅ lowerStar k₀ l φ ⋙ constantTwist k₀ l Y b :=
  IsoAlgebra.twistCompMapOfNatIsoIso
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ _))
    (frobeniusPullbackSmulIso k₀ l X b) (frobeniusPullbackSmulIso k₀ l Y b)
    (smul_comp_hom_app (AdicSheaf.adicLowerStar_map_smul _) _ _)

variable (k₀ l) in
/-- The derived pushforward of pro-étale Weil sheaves commutes with constant twists. -/
noncomputable def mapDerivedCategoryConstantTwistCompIso :
    (constantTwist k₀ l X b).mapDerivedCategory ⋙ (lowerStar k₀ l φ).rightDerivedFunctor ≅
      (lowerStar k₀ l φ).rightDerivedFunctor ⋙ (constantTwist k₀ l Y b).mapDerivedCategory :=
  IsoAlgebra.mapDerivedCategoryTwistCompIso
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ _))
    (frobeniusPullbackSmulIso k₀ l X b) (frobeniusPullbackSmulIso k₀ l Y b)
    (smul_comp_hom_app (AdicSheaf.adicLowerStar_map_smul _) _ _)



variable (k₀ l) in
/-- A transport of pro-étale Weil sheaves along a functor commuting with multiplication by
scalars commutes with constant twists. -/
noncomputable def constantTwistCompMapOfNatIsoIso {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))]
    {L : AdicSheaf l (U ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hL : ∀ c M, L.map (AdicSheaf.smul c M) = AdicSheaf.smul c (L.obj M))
    (e : L ⋙ WeilSheaf.frobeniusPullback k₀ l X ≅ WeilSheaf.frobeniusPullback k₀ l U ⋙ L) :
    constantTwist k₀ l U b ⋙ IsoAlgebra.mapOfNatIso e ≅
      IsoAlgebra.mapOfNatIso e ⋙ constantTwist k₀ l X b :=
  IsoAlgebra.twistCompMapOfNatIsoIso e _ _ (smul_comp_hom_app hL e _)

section LowerShriek

variable [Fact (ringChar k₀ ≠ l)] {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over

variable (k₀ l) in
/-- The extension by zero of pro-étale Weil sheaves commutes with constant twists. -/
noncomputable def constantTwistCompExtensionByZeroIso (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    constantTwist k₀ l U b ⋙ extensionByZero k₀ l j ≅
      extensionByZero k₀ l j ⋙ constantTwist k₀ l X b :=
  -- Passing the transport isomorphism through `constantTwistCompMapOfNatIsoIso` keeps the
  -- kernel from unfolding it.
  constantTwistCompMapOfNatIsoIso k₀ l b (AdicSheaf.adicOpenImmersionLowerShriek_map_smul _)
    (adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l j (comp_over j _))

variable (k₀ l) in
/-- The derived extension by zero of pro-étale Weil sheaves commutes with constant twists. -/
noncomputable def mapDerivedCategoryConstantTwistCompExtensionByZeroIso (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    (constantTwist k₀ l U b).mapDerivedCategory ⋙ (extensionByZero k₀ l j).mapDerivedCategory ≅
      (extensionByZero k₀ l j).mapDerivedCategory ⋙ (constantTwist k₀ l X b).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (constantTwistCompExtensionByZeroIso k₀ l b j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

variable (k₀ l) in
/-- The direct image with compact support of pro-étale Weil sheaves commutes with constant
twists. -/
noncomputable def mapDerivedCategoryConstantTwistCompRightDerivedLowerShriekIso
    (c : Compactification φ) :
    (constantTwist k₀ l X b).mapDerivedCategory ⋙ rightDerivedLowerShriek k₀ l φ c ≅
      rightDerivedLowerShriek k₀ l φ c ⋙ (constantTwist k₀ l Y b).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryConstantTwistCompExtensionByZeroIso k₀ l b c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (mapDerivedCategoryConstantTwistCompIso k₀ l c.g b) ≪≫
    (Functor.associator _ _ _).symm

end LowerShriek
end ProEtaleWeilSheaf

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The cohomology sheaves of the direct image `Ra_*(F ⊗ 𝓑_b)` along the structure morphism
`a : Y ⟶ Spec k₀` are the constant twists of those of `Ra_* F`. -/
noncomputable def homologySheafDerivedLowerStarConstantTwistIso (F : WeilSheaf k₀ l Y)
    (b : (PadicAlgCl l)ˣ) (r : ℤ) :
    (WeilComplex.homologySheaf r).obj ((WeilComplex.derivedLowerStar
        (Y ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj (F.constantTwist b))) ≅
      ((WeilComplex.homologySheaf r).obj ((WeilComplex.derivedLowerStar
        (Y ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj F))).constantTwist b :=
  ObjectProperty.isoMk _
    ((_root_.DerivedCategory.homologyFunctor _ r).mapIso
        ((ProEtaleWeilSheaf.lowerStar k₀ l
            (Y ↘ Spec (CommRingCat.of k₀))).rightDerivedFunctor.mapIso
          ((_root_.DerivedCategory.singleFunctor _ 0).mapIso (F.constantTwistObjIso b) ≪≫
            ((ProEtaleWeilSheaf.constantTwist k₀ l Y b).mapDerivedCategorySingleFunctor 0).symm.app
              F.obj) ≪≫
          (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompIso k₀ l
            (Y ↘ Spec (CommRingCat.of k₀)) b).app _) ≪≫
      ((ProEtaleWeilSheaf.constantTwist k₀ l _ b).mapDerivedCategoryHomologyFunctorIso r).symm.app
        _ ≪≫
      (ProEtaleWeilSheaf.mkConstantTwistIso k₀ l _ _ b).symm)

/-- **Cohomology of a constant twist.** The cohomology `Hʳ(Y ⊗ k̄, F ⊗ 𝓑_b)` of the constant
Weil twist of `F` by a unit `b ∈ ℚ̄_ℓˣ` is `Hʳ(Y ⊗ k̄, F)` with the geometric Frobenius multiplied
by `b`. -/
theorem nonempty_equiv_cohomology_constantTwist (F : WeilSheaf k₀ l Y) (b : (PadicAlgCl l)ˣ)
    (r : ℤ) : Nonempty (((F.constantTwist b).cohomology r).Equiv ((F.cohomology r).rescale b)) :=
  ⟨(globalSectionsEquivOfIso (homologySheafDerivedLowerStarConstantTwistIso F b r)).trans
    (globalSectionsConstantTwistEquiv _ b)⟩


section CompactSupport

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The cohomology sheaves of the direct image with compact support `Ra_!(F ⊗ 𝓑_b)` along the
structure morphism `a : X ⟶ Spec k₀` are the constant twists of those of `Ra_! F`. -/
noncomputable def homologySheafDerivedLowerShriekConstantTwistIso (F : WeilSheaf k₀ l X)
    (b : (PadicAlgCl l)ˣ) (r : ℤ) :
    (WeilComplex.homologySheaf r).obj ((WeilComplex.derivedLowerShriek k₀ l
        (X ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj (F.constantTwist b))) ≅
      ((WeilComplex.homologySheaf r).obj ((WeilComplex.derivedLowerShriek k₀ l
        (X ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj F))).constantTwist b :=
  ObjectProperty.isoMk _
    ((_root_.DerivedCategory.homologyFunctor _ r).mapIso
        ((ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))
            (HasCompactification.compactification _
              (hf := hasCompactification_of_over (k₀ := k₀) _))).mapIso
          ((_root_.DerivedCategory.singleFunctor _ 0).mapIso (F.constantTwistObjIso b) ≪≫
            ((ProEtaleWeilSheaf.constantTwist k₀ l X b).mapDerivedCategorySingleFunctor 0).symm.app
              F.obj) ≪≫
          (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompRightDerivedLowerShriekIso k₀ l
            (X ↘ Spec (CommRingCat.of k₀)) b _).app _) ≪≫
      ((ProEtaleWeilSheaf.constantTwist k₀ l _ b).mapDerivedCategoryHomologyFunctorIso r).symm.app
        _ ≪≫
      (ProEtaleWeilSheaf.mkConstantTwistIso k₀ l _ _ b).symm)

/-- **Compactly supported cohomology of a constant twist.** The compactly supported cohomology
`H_cʳ(X ⊗ k̄, F ⊗ 𝓑_b)` of the constant Weil twist of `F` by a unit `b ∈ ℚ̄_ℓˣ` is
`H_cʳ(X ⊗ k̄, F)` with the geometric Frobenius multiplied by `b`. -/
theorem nonempty_equiv_compactlySupportedCohomology_constantTwist (F : WeilSheaf k₀ l X)
    (b : (PadicAlgCl l)ˣ) (r : ℤ) :
    Nonempty (((F.constantTwist b).compactlySupportedCohomology r).Equiv
      ((F.compactlySupportedCohomology r).rescale b)) :=
  ⟨(globalSectionsEquivOfIso (homologySheafDerivedLowerShriekConstantTwistIso F b r)).trans
    (globalSectionsConstantTwistEquiv _ b)⟩

end CompactSupport

section HigherLowerShriek

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- **Constant twists and higher direct images with compact support**: for a morphism
`f : X ⟶ Y` of `k₀`-schemes as in `AlgebraicGeometry.WeilSheaf.higherLowerShriek` and a unit
`b ∈ ℚ̄_ℓˣ`, `Rⁱf₀!(F ⊗ 𝓑_b) ≅ Rⁱf₀!F ⊗ 𝓑_b`. The direct image with compact support of
pro-étale Weil sheaves commutes with constant twists, its constituents being `ℚ̄_ℓ`-linear.
(blueprint: `proposition-purity-lisse-part-fourier-transform`) -/
theorem nonempty_higherLowerShriek_constantTwist_iso (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) (i : ℕ) :
    Nonempty ((higherLowerShriek k₀ l f i).obj (F.constantTwist b) ≅
      ((higherLowerShriek k₀ l f i).obj F).constantTwist b) :=
  ⟨ObjectProperty.isoMk _
    ((_root_.DerivedCategory.homologyFunctor _ i).mapIso
        ((ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f
            (HasCompactification.compactification _
              (hf := hasCompactification_of_over (k₀ := k₀) _))).mapIso
          ((_root_.DerivedCategory.singleFunctor _ 0).mapIso (F.constantTwistObjIso b) ≪≫
            ((ProEtaleWeilSheaf.constantTwist k₀ l X b).mapDerivedCategorySingleFunctor 0).symm.app
              F.obj) ≪≫
          (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompRightDerivedLowerShriekIso k₀ l
            f b _).app _) ≪≫
      ((ProEtaleWeilSheaf.constantTwist k₀ l _ b).mapDerivedCategoryHomologyFunctorIso i).symm.app
        _ ≪≫
      (ProEtaleWeilSheaf.mkConstantTwistIso k₀ l _ _ b).symm)⟩

end HigherLowerShriek

end WeilSheaf

end AlgebraicGeometry
