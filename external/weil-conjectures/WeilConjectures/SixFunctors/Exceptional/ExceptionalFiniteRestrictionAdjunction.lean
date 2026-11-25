/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalRealizationShift

/-!
# Realizations and normalized restricted finite-coefficient adjunctions

Source: Zheng, Propositions 2.23, 2.29, 3.16, Lemma 5.22 and Proposition 5.24;
blueprint exceptional inverse-image construction
(blueprint: def-sf-finite-operation-realizations).

The categories are the published full intrinsic constant-coefficient categories.
The normalization is expressed in their canonical fixed-module coordinates, using
exactly the specified-compactification ordinary etale adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures

/-- Finiteness at a positive level, with the existing coefficient quotient unchanged.
Source: Zheng, finite coefficient convention
(blueprint: lem-sf-exceptional-finite-operations). -/
instance sfFiniteOperationsCoefficientFinite (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+) :
    Finite (Padic.coefficientExtensionRing l E.carrier n) :=
  Padic.finite_coefficientExtensionRing l E.carrier n n.pos

/-- The ordinary etale adjoint at this specified compactification is supplied by the
published Brown theorem, rather than by an assumed ambient pro-etale adjunction.
Source: Zheng, Proposition 2.23 (blueprint: lem-sf-exceptional-finite-operations). -/
instance sfFiniteOperationsEtaleLeftAdjoint (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) c).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c

/-- The full inclusion followed by the canonical coefficient realization inverse.
This changes coefficient coordinates only, retaining all ambient derived morphisms.
Source: blueprint full finite-Tor categories and site comparison
(blueprint: lem-sf-exceptional-finite-operations). -/
abbrev sfFiniteOperationsRealization (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+) (T : Scheme.{u}) :=
  (finiteTorConstructible l E.carrier n n.pos T).ι ⋙
    (sfIntrinsicDerivedEquivalence T (Padic.coefficientExtensionRing l E.carrier n)).inverse

/-- The realization uses the termwise exact coefficient equivalence and the full
triangulated inclusion, hence their canonical derived shifts.
Source: blueprint ambient integer-shift realization
(blueprint: lem-sf-exceptional-finite-operations). -/
instance sfFiniteOperationsRealizationShift (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+) (T : Scheme.{u}) :
    (sfFiniteOperationsRealization l E n T).CommShift ℤ :=
  inferInstanceAs (((finiteTorConstructible l E.carrier n n.pos T).ι ⋙
    (sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing l E.carrier n)).inverse.mapDerivedCategory).CommShift ℤ)

/-- The specified etale right adjoint has the adjoint shift structure.
Source: Zheng, Proposition 2.23
(blueprint: lem-sf-exceptional-finite-operations). -/
instance sfFiniteOperationsEtaleRightShift (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) c).rightAdjoint.CommShift ℤ :=
  (Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) c)).rightAdjointCommShift ℤ

/-- The fixed-coordinate exceptional composite uses the derived comparison shifts.
Source: blueprint exceptional inverse image
(blueprint: lem-sf-exceptional-finite-operations). -/
instance sfFiniteOperationsExceptionalShift (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (ProEtale.sfFiniteExceptionalAt
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) c).CommShift ℤ :=
  inferInstanceAs (((ProEtale.comparisonLowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E.carrier n))) Y).rightDerivedFunctor ⋙
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) c).rightAdjoint ⋙
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) X).mapDerivedCategory).CommShift ℤ)

/-- The intrinsic conjugate of the specified-c exceptional functor. Parentheses retain
its canonical coefficient cancellation, with no freely chosen realization.
Source: blueprint exceptional inverse image
(blueprint: lem-sf-exceptional-finite-operations). -/
def sfFiniteOperationsIntrinsicRight (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E.carrier n)).inverse ⋙
    ProEtale.sfFiniteExceptionalAt
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) c) ⋙
    (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E.carrier n)).functor

/-- The inverse-coordinate compact-support comparison, obtained only by cancellation
of the unit and counit in the published normalized comparison.
Source: blueprint proper/open comparison
(blueprint: lem-sf-exceptional-finite-operations). -/
def sfFiniteOperationsSupportComparison (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E.carrier n) ⋙
        (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E.carrier n)).inverse ≅
      (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E.carrier n)).inverse ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E.carrier n))) c :=
  (Iso.inverseCompIso
    ((Iso.compInverseIso (ProEtale.sfIntrinsicCompactSupportComparison
      (Padic.coefficientExtensionRing l E.carrier n) c)).symm ≪≫
        Functor.associator _ _ _)).symm

/-- The realization of a literal restriction of the recorded intrinsic support functor.
The equality fixes objects and morphisms; its proof cannot absorb an automorphism.
Source: blueprint full finite-Tor restriction
(blueprint: lem-sf-exceptional-finite-operations). -/
def sfFiniteOperationsLeftRealization (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (F : finiteTorConstructibleCategory l E.carrier n n.pos X ⥤
      finiteTorConstructibleCategory l E.carrier n n.pos Y)
    (eF : F ⋙ (finiteTorConstructible l E.carrier n n.pos Y).ι =
      (finiteTorConstructible l E.carrier n n.pos X).ι ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E.carrier n)) :
    F ⋙ sfFiniteOperationsRealization l E n Y ≅
      sfFiniteOperationsRealization l E n X ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E.carrier n))) c :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso eF) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfFiniteOperationsSupportComparison l E n c) ≪≫
    (Functor.associator _ _ _).symm

/-- The exceptional realization cancels only the coefficient-equivalence unit.
Its equality hypothesis fixes the restriction on both objects and morphisms.
Source: blueprint full finite-Tor restriction
(blueprint: lem-sf-exceptional-finite-operations). -/
def sfFiniteOperationsRightRealization (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (G : finiteTorConstructibleCategory l E.carrier n n.pos Y ⥤
      finiteTorConstructibleCategory l E.carrier n n.pos X)
    (eG : G ⋙ (finiteTorConstructible l E.carrier n n.pos X).ι =
      (finiteTorConstructible l E.carrier n n.pos Y).ι ⋙
        sfFiniteOperationsIntrinsicRight l E n c) :
    G ⋙ sfFiniteOperationsRealization l E n X ≅
      sfFiniteOperationsRealization l E n Y ⋙ ProEtale.sfFiniteExceptionalAt
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) c :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso eG) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Iso.compInverseIso (Iso.refl _)) ≪≫
    (Functor.associator _ _ _).symm

/-- The actual normalized Hom chain, specialized to the quasi-compact field-scheme
case without requiring separated structure maps. Its factors are the proper/open
comparison, the comparison adjunction, the specified ordinary etale adjunction,
comparison full faithfulness, and the retained etale-origin isomorphism.
Source: Zheng, Proposition 2.23, and blueprint class adjunction, clause (2)
(blueprint: lem-sf-exceptional-finite-operations). -/
def sfFiniteOperationsHomEquiv (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    (k : Type u) [Field k] {X Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
    {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)))))
    (W : FixedEtaleOriginWitness X
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n))))) :
    ((ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) c).obj M.obj ⟶ L.obj) ≃
      (M.obj ⟶ (ProEtale.sfFiniteExceptionalAt
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) c).obj L.obj) :=
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  ProEtale.specifiedExceptionalHomEquiv _ c M W L

private theorem sfTransposeLeft
    {E₀ E₁ C₀ C₁ : Type*} [Category* E₀] [Category* E₁]
    [Category* C₀] [Category* C₁]
    (A : E₀ ⥤ C₀) (B : E₁ ⥤ C₁) (U : C₁ ⥤ E₁)
    (F : E₀ ⥤ E₁) (R : E₁ ⥤ E₀) (I : C₀ ⥤ C₁)
    (ad : F ⊣ R) (bd : B ⊣ U)
    {L L' : E₀} {M M' : C₀} {N : C₁}
    (a : A.obj L ≅ M) (a' : A.obj L' ≅ M')
    (v : B.obj (F.obj L) ⟶ I.obj (A.obj L))
    (v' : B.obj (F.obj L') ⟶ I.obj (A.obj L'))
    (s : M ⟶ M') (b : I.obj M' ⟶ N) (t : L ⟶ L')
    (ht : A.map t = a.hom ≫ s ≫ a'.inv)
    (hv : B.map (F.map t) ≫ v' = v ≫ I.map (A.map t)) :
    a.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v ≫ I.map a.hom ≫ I.map s ≫ b))) =
    s ≫ a'.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v' ≫ I.map a'.hom ≫ b))) := by
  have hm : A.map t ≫ a'.hom = a.hom ≫ s := by
    rw [ht]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have heq : v ≫ I.map a.hom ≫ I.map s ≫ b =
      B.map (F.map t) ≫ v' ≫ I.map a'.hom ≫ b := by
    rw [reassoc_of% hv, ← I.map_comp_assoc, ← I.map_comp_assoc, hm, I.map_comp,
      Category.assoc]
  rw [heq, bd.homEquiv_naturality_left, ad.homEquiv_naturality_left, A.map_comp]
  simp only [← Category.assoc]
  congr 1
  rw [ht]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem sfSpecifiedHomValue
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint]
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (W : FixedEtaleOriginWitness X Λ M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (a : (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c).obj M.obj ⟶ L.obj) :
    ProEtale.specifiedExceptionalHomEquiv Λ c M W L a = W.iso.inv ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
        ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} Λ) c)).homEquiv _ _
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ _
            ((ProEtale.fixedCompactSupportComparisonIso Λ c).inv.app W.complex ≫
              (ProEtale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} Λ) c).map W.iso.hom ≫ a))) := by
  rfl

private theorem sfSpecifiedHomLeft
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint]
    (M M' : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (W : FixedEtaleOriginWitness X Λ M) (W' : FixedEtaleOriginWitness X Λ M')
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (s : M.obj ⟶ M'.obj)
    (a : (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c).obj M'.obj ⟶ L.obj) :
    ProEtale.specifiedExceptionalHomEquiv Λ c M W L
      ((ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} Λ) c).map s ≫ a) =
      s ≫ ProEtale.specifiedExceptionalHomEquiv Λ c M' W' L a := by
  obtain ⟨t, ht⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
    W.complex.obj W'.complex.obj W'.complex.property).surjective
      (W.iso.hom ≫ s ≫ W'.iso.inv)
  have hv := (ProEtale.fixedCompactSupportComparisonIso Λ c).inv.naturality
    (ObjectProperty.homMk t : W.complex ⟶ W'.complex)
  rw [sfSpecifiedHomValue, sfSpecifiedHomValue]
  exact sfTransposeLeft _ _ _ _ _ _
    (Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c))
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y)
    W.iso W'.iso _ _ s a t ht hv

private theorem sfSpecifiedHomRight
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint]
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (W : FixedEtaleOriginWitness X Λ M)
    (L L' : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (a : (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c).obj M.obj ⟶ L.obj) (b : L.obj ⟶ L'.obj) :
    ProEtale.specifiedExceptionalHomEquiv Λ c M W L' (a ≫ b) =
      ProEtale.specifiedExceptionalHomEquiv Λ c M W L a ≫
        (ProEtale.sfFiniteExceptionalAt Λ c).map b := by
  rw [sfSpecifiedHomValue, sfSpecifiedHomValue]
  simp only [← Category.assoc]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    Functor.map_comp]
  simp only [Category.assoc]
  rfl

private theorem sfRestrictHom
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (RX : C ⥤ C') (RY : D ⥤ D') [RX.Full] [RX.Faithful] [RY.Full] [RY.Faithful]
    (P : C' ⥤ D') (H : D' ⥤ C') (F : C ⥤ D) (G : D ⥤ C)
    (rF : F ⋙ RY ≅ RX ⋙ P) (rG : G ⋙ RX ≅ RY ⋙ H)
    (e : ∀ K L, (P.obj (RX.obj K) ⟶ RY.obj L) ≃ (RX.obj K ⟶ H.obj (RY.obj L)))
    (hleft : ∀ {K K'} (s : K ⟶ K') (L) (a : P.obj (RX.obj K') ⟶ RY.obj L),
      e K L (P.map (RX.map s) ≫ a) = RX.map s ≫ e K' L a)
    (hright : ∀ (K) {L L'} (a : P.obj (RX.obj K) ⟶ RY.obj L) (b : L ⟶ L'),
      e K L' (a ≫ RY.map b) = e K L a ≫ H.map (RY.map b)) :
    ∃ adj : F ⊣ G, ∀ K L (a : F.obj K ⟶ L),
      RX.map (adj.homEquiv K L a) ≫ rG.hom.app L =
        e K L (rF.inv.app K ≫ RY.map a) := by
  let ffX := Functor.FullyFaithful.ofFullyFaithful RX
  let ffY := Functor.FullyFaithful.ofFullyFaithful RY
  let ψ (K : C) (L : D) : (F.obj K ⟶ L) ≃ (K ⟶ G.obj L) :=
    ffY.homEquiv.trans (((rF.app K).homFromEquiv.trans (e K L)).trans
      (((rG.app L).symm.homToEquiv).trans ffX.homEquiv.symm))
  have hn (K : C) (L : D) (a : F.obj K ⟶ L) :
      RX.map (ψ K L a) ≫ rG.hom.app L =
        e K L (rF.inv.app K ≫ RY.map a) := by
    dsimp only [ψ, Equiv.trans_apply, Functor.FullyFaithful.homEquiv,
      Iso.homFromEquiv, Iso.homToEquiv, Equiv.symm, Equiv.coe_fn_mk]
    rw [ffX.map_preimage]
    simp only [Category.assoc]
    change e K L (rF.inv.app K ≫ RY.map a) ≫ rG.inv.app L ≫ rG.hom.app L = _
    rw [Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hl {K K' : C} (s : K ⟶ K') (L : D) (a : F.obj K' ⟶ L) :
      ψ K L (F.map s ≫ a) = s ≫ ψ K' L a := by
    apply RX.map_injective
    apply (cancel_mono (rG.hom.app L)).1
    rw [hn, RX.map_comp, Category.assoc, hn]
    have hnat := rF.inv.naturality s
    dsimp only [Functor.comp_map] at hnat
    rw [RY.map_comp, ← Category.assoc, ← hnat, Category.assoc]
    change e K L ((RX ⋙ P).map s ≫ rF.inv.app K' ≫ RY.map a) = _
    exact hleft s L _
  have hr (K : C) {L L' : D} (a : F.obj K ⟶ L) (b : L ⟶ L') :
      ψ K L' (a ≫ b) = ψ K L a ≫ G.map b := by
    apply RX.map_injective
    apply (cancel_mono (rG.hom.app L')).1
    have hnat := rG.hom.naturality b
    dsimp only [Functor.comp_map] at hnat
    rw [hn, RX.map_comp, Category.assoc, hnat]
    change _ = RX.map (ψ K L a) ≫ rG.hom.app L ≫ H.map (RY.map b)
    rw [← Category.assoc, hn, RY.map_comp, ← Category.assoc, hright]
  let core : Adjunction.CoreHomEquiv F G :=
    { homEquiv := ψ
      homEquiv_naturality_left_symm := by
        intro K K' L s a
        apply (ψ K L).injective
        rw [Equiv.apply_symm_apply, hl, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun {_ _ _} a b ↦ hr _ a b }
  exact ⟨Adjunction.mkOfHomEquiv core, fun K L a ↦ by
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    change RX.map (ψ K L a) ≫ rG.hom.app L = _
    exact hn K L a⟩

private theorem sfRestrictionOrigin (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    (T : Scheme.{u}) (K : finiteTorConstructibleCategory l E.carrier n n.pos T) :
    ∃ h : DerivedCategory.TStructure.t.plus ((sfFiniteOperationsRealization l E n T).obj K),
      Nonempty (FixedEtaleOriginWitness T
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n))
        ⟨(sfFiniteOperationsRealization l E n T).obj K, h⟩) := by
  classical
  let A := Padic.coefficientExtensionRing l E.carrier n
  let R := sfIntrinsicDerivedEquivalence T A
  let U := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  obtain ⟨a, ha⟩ := K.property.1.1.bddBelow
  obtain ⟨b, hb⟩ := K.property.1.1.bddAbove
  have hv : ∀ i : ℤ, (i < min a b ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj) := by
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hi
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin T A).2.2.1
    K.obj).mpr ⟨K.property.1.2, min a b, b, min_le_right _ _, hv⟩
  let hL : DerivedCategory.TStructure.t.plus L.obj := by
    obtain ⟨c, d, _, hcd⟩ := L.property.2
    exact ⟨c, (DerivedCategory.isGE_iff L.obj c).2 (fun i hi ↦ hcd i (.inl hi))⟩
  let e : U.mapDerivedCategory.obj L.obj ≅ R.inverse.obj K.obj :=
    R.functor.preimageIso
      (((Functor.mapDerivedCategoryCompIso U
        (sfIntrinsicModuleEquivalence T A).functor).app L.obj) ≪≫
        eL ≪≫ (R.counitIso.app K.obj).symm)
  have hU : DerivedCategory.TStructure.t.plus (U.mapDerivedCategory.obj L.obj) := by
    obtain ⟨c, hc⟩ := hL
    refine ⟨c, (DerivedCategory.isGE_iff _ c).2 (fun i hi ↦ ?_)⟩
    exact U.isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isGE_iff L.obj c).1 hc i hi)
  have h : DerivedCategory.TStructure.t.plus (R.inverse.obj K.obj) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso e hU
  exact ⟨h, ⟨⟨⟨L.obj, hL⟩, e⟩⟩⟩

private instance sfRestrictionRealizationFull (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+) (T : Scheme.{u}) :
    (sfFiniteOperationsRealization l E n T).Full := by
  dsimp only [sfFiniteOperationsRealization]
  infer_instance

private instance sfRestrictionRealizationFaithful (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+) (T : Scheme.{u}) :
    (sfFiniteOperationsRealization l E n T).Faithful := by
  dsimp only [sfFiniteOperationsRealization]
  infer_instance

private instance sfRestrictionRealizationAdditive (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+) (T : Scheme.{u}) :
    (sfFiniteOperationsRealization l E n T).Additive :=
  inferInstanceAs (((finiteTorConstructible l E.carrier n n.pos T).ι ⋙
    (sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing l E.carrier n)).inverse.mapDerivedCategory).Additive)

private instance sfRestrictionRealizationIsTriangulated (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+) (T : Scheme.{u}) :
    (sfFiniteOperationsRealization l E n T).IsTriangulated :=
  inferInstanceAs (((finiteTorConstructible l E.carrier n n.pos T).ι ⋙
    (sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing l E.carrier n)).inverse.mapDerivedCategory).IsTriangulated)

/-- Restrict the normalized site-comparison Hom chain to fixed finite-Tor functors.
No preservation or uniform-bound assertion is part of this lemma: both literal
restrictions are inputs. The output fixes the left exact structure and the right
adjoint shifts, including the canonical realization maps.
Source: Zheng, Proposition 2.23; blueprint exceptional construction, steps 4--5
(blueprint: lem-sf-finite-restriction-normalized-adjunction).

Proof: Constructible origin provides a bounded-below etale complex for each input.
Use the proper/open comparison followed by the comparison adjunction, the ordinary
etale adjunction for the specified compactification, and comparison full faithfulness.
Retain the origin isomorphism at both ends. Full faithfulness of the inclusions and
of coefficient realization transports this Hom equivalence to the two full
subcategories. Naturality in both arguments follows from naturality of each factor;
changing origin gives the same map by full faithfulness of comparison. Apply
Adjunction.mkOfHomEquiv to obtain the adjunction. Restrict the ambient derived left
shift and distinguished triangles. Use its adjoint shifts on the right; the
comparison units, counits and proper/open derived comparisons commute with shifts,
so the two prescribed realization maps do also. Their factors are precisely those
in sfFiniteOperationsHomEquiv, giving the displayed normalization for every origin.
The bounded-below witnesses come from bounded constructibility and the exact
coefficient equivalence. Empty schemes and zero objects require no nonemptiness
choices and satisfy the same natural Hom formulas. -/
theorem sfFiniteOperations_restrictedAdjunction (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    (F : finiteTorConstructibleCategory l E.carrier n n.pos X ⥤
          finiteTorConstructibleCategory l E.carrier n n.pos Y)
      (G : finiteTorConstructibleCategory l E.carrier n n.pos Y ⥤
          finiteTorConstructibleCategory l E.carrier n n.pos X)
      (eF : F ⋙ (finiteTorConstructible l E.carrier n n.pos Y).ι =
        (finiteTorConstructible l E.carrier n n.pos X).ι ⋙
          sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E.carrier n))
      (eG : G ⋙ (finiteTorConstructible l E.carrier n n.pos X).ι =
        (finiteTorConstructible l E.carrier n n.pos Y).ι ⋙
          sfFiniteOperationsIntrinsicRight l E n c) :
    ∃ (_ : F.Additive) (_ : F.CommShift ℤ) (adj : F ⊣ G),
    letI := adj.rightAdjointCommShift ℤ
    F.IsTriangulated ∧
      ∃ (rF : F ⋙ sfFiniteOperationsRealization l E n Y ≅
          sfFiniteOperationsRealization l E n X ⋙
            ProEtale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1, u}
                (Padic.coefficientExtensionRing l E.carrier n))) c)
        (rG : G ⋙ sfFiniteOperationsRealization l E n X ≅
          sfFiniteOperationsRealization l E n Y ⋙ ProEtale.sfFiniteExceptionalAt
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) c)
        (hX : ∀ K : finiteTorConstructibleCategory l E.carrier n n.pos X,
          DerivedCategory.TStructure.t.plus ((sfFiniteOperationsRealization l E n X).obj K))
        (hY : ∀ L : finiteTorConstructibleCategory l E.carrier n n.pos Y,
          DerivedCategory.TStructure.t.plus ((sfFiniteOperationsRealization l E n Y).obj L)),
      rF = sfFiniteOperationsLeftRealization l E n c F eF ∧
      rG = sfFiniteOperationsRightRealization l E n c G eG ∧
      rF.hom.CommShift ℤ ∧ rG.hom.CommShift ℤ ∧
      (∀ K : finiteTorConstructibleCategory l E.carrier n n.pos X,
        Nonempty (FixedEtaleOriginWitness X
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n))
          ⟨(sfFiniteOperationsRealization l E n X).obj K, hX K⟩)) ∧
      (∀ (K : finiteTorConstructibleCategory l E.carrier n n.pos X)
        (L : finiteTorConstructibleCategory l E.carrier n n.pos Y)
        (W : FixedEtaleOriginWitness X
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n))
          ⟨(sfFiniteOperationsRealization l E n X).obj K, hX K⟩) (a : F.obj K ⟶ L),
        (sfFiniteOperationsRealization l E n X).map (adj.homEquiv K L a) ≫ rG.hom.app L =
          sfFiniteOperationsHomEquiv l E n D.k (Y ↘ Spec (.of D.k)) c
            ⟨(sfFiniteOperationsRealization l E n X).obj K, hX K⟩ W
            ⟨(sfFiniteOperationsRealization l E n Y).obj L, hY L⟩
            (rF.inv.app K ≫ (sfFiniteOperationsRealization l E n Y).map a)) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  let A := Padic.coefficientExtensionRing l E.carrier n
  let Λ := ULift.{u + 1, u} A
  let RX := sfFiniteOperationsRealization l E n X
  let RY := sfFiniteOperationsRealization l E n Y
  let P := ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c
  let H := ProEtale.sfFiniteExceptionalAt Λ c
  let rF := sfFiniteOperationsLeftRealization l E n c F eF
  let rG := sfFiniteOperationsRightRealization l E n c G eG
  have : (RX ⋙ P).Additive := inferInstance
  have : (F ⋙ RY).Additive := Functor.additive_of_iso rF.symm
  have : F.Additive := Functor.additive_of_comp_faithful F RY
  let : F.CommShift ℤ := Functor.CommShift.ofComp rF ℤ
  have : rF.hom.CommShift ℤ := Functor.CommShift.ofComp_compatibility rF ℤ
  have : F.IsTriangulated := (Functor.isTriangulated_iff_comp_right rF).2 inferInstance
  let hX (K : finiteTorConstructibleCategory l E.carrier n n.pos X) :
      DerivedCategory.TStructure.t.plus (RX.obj K) :=
    (sfRestrictionOrigin l E n X K).choose
  let hY (L : finiteTorConstructibleCategory l E.carrier n n.pos Y) :
      DerivedCategory.TStructure.t.plus (RY.obj L) :=
    (sfRestrictionOrigin l E n Y L).choose
  have origin (K : finiteTorConstructibleCategory l E.carrier n n.pos X) :
      Nonempty (FixedEtaleOriginWitness X Λ ⟨RX.obj K, hX K⟩) :=
    (sfRestrictionOrigin l E n X K).choose_spec
  let wX (K : finiteTorConstructibleCategory l E.carrier n n.pos X) :
      FixedEtaleOriginWitness X Λ ⟨RX.obj K, hX K⟩ := Classical.choice (origin K)
  let e (K : finiteTorConstructibleCategory l E.carrier n n.pos X)
      (L : finiteTorConstructibleCategory l E.carrier n n.pos Y) :
      (P.obj (RX.obj K) ⟶ RY.obj L) ≃ (RX.obj K ⟶ H.obj (RY.obj L)) :=
    ProEtale.specifiedExceptionalHomEquiv Λ c
      ⟨RX.obj K, hX K⟩ (wX K) ⟨RY.obj L, hY L⟩
  have heLeft {K K'} (s : K ⟶ K') (L) (a : P.obj (RX.obj K') ⟶ RY.obj L) :
      e K L (P.map (RX.map s) ≫ a) = RX.map s ≫ e K' L a := by
    dsimp only [e]
    exact sfSpecifiedHomLeft Λ c ⟨RX.obj K, hX K⟩ ⟨RX.obj K', hX K'⟩
      (wX K) (wX K') ⟨RY.obj L, hY L⟩ (RX.map s) a
  have heRight (K) {L L'} (a : P.obj (RX.obj K) ⟶ RY.obj L) (b : L ⟶ L') :
      e K L' (a ≫ RY.map b) = e K L a ≫ H.map (RY.map b) := by
    dsimp only [e]
    exact sfSpecifiedHomRight Λ c ⟨RX.obj K, hX K⟩ (wX K)
      ⟨RY.obj L, hY L⟩ ⟨RY.obj L', hY L'⟩ a (RY.map b)
  obtain ⟨adj, hn⟩ := sfRestrictHom RX RY P H F G rF rG e heLeft heRight
  have hnAll (K : finiteTorConstructibleCategory l E.carrier n n.pos X)
      (L : finiteTorConstructibleCategory l E.carrier n n.pos Y)
      (W : FixedEtaleOriginWitness X Λ ⟨RX.obj K, hX K⟩)
      (a : F.obj K ⟶ L) :
      RX.map (adj.homEquiv K L a) ≫ rG.hom.app L =
        ProEtale.specifiedExceptionalHomEquiv Λ c ⟨RX.obj K, hX K⟩ W
          ⟨RY.obj L, hY L⟩ (rF.inv.app K ≫ RY.map a) := by
    rw [hn]
    have h := sfSpecifiedHomLeft Λ c ⟨RX.obj K, hX K⟩ ⟨RX.obj K, hX K⟩ (wX K) W
      ⟨RY.obj L, hY L⟩ (𝟙 _) (rF.inv.app K ≫ RY.map a)
    change e K L (P.map (𝟙 (RX.obj K)) ≫ rF.inv.app K ≫ RY.map a) =
      (𝟙 (RX.obj K)) ≫ _ at h
    rw [P.map_id, Category.id_comp, Category.id_comp] at h
    exact h
  have hs := ProEtale.specifiedExceptionalRealization_shift Λ c RX RY F G adj
    rF rG hX hY origin hnAll
  refine ⟨inferInstance, inferInstance, adj, inferInstance, rF, rG, hX, hY,
    rfl, rfl, inferInstance, hs, origin, ?_⟩
  exact hnAll

end WeilConjectures
