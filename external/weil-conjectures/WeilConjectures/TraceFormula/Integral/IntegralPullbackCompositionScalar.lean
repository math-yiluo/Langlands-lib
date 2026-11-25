/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralPullbackCompositionScalarBase
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence

/-! # Scalar extension carries the integral pullback compositor

Source: Stacks Project, Tags 06YY, 07A4, 0941 and 0D6D; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-composition-scalar).

For a coefficient inclusion E to L, completed scalar extension carries the specified
integral composition comparison at E to the one at L, conjugated by the canonical
scalar/pullback comparisons. Both sides are compared after the fully faithful coherent
reduction at L: the system-level composition clause of integralPullbackComposition at
E and at L, the system scalar comparison, the pullback/scalar square of
scalarExtensionTowerCoherence, and whole-system mixed coherence.
The rationalized statement follows by localization on pure tensors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section SystemScalar
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategoryFactors integralComparisonSequenceScalarModel
attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar

set_option allowUnsafeReducibility true in
attribute [local reducible] integralSystemReduction

/-- Scalar extension with the finite-system source and target displayed explicitly. -/
private abbrev integralCompositionFiniteScalar (X : Scheme.{u}) :
    finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) X ⥤
      finiteSystemDerived (integralSystemRings l L) (integralSystemTransition l L) X :=
  integralComparisonDerivedSequenceScalar l E L ι X

private abbrev integralCompositionFiniteScalarPullback {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :
    finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E) f ⋙
        integralCompositionFiniteScalar l E L ι X ≅
      integralCompositionFiniteScalar l E L ι Y ⋙
        finiteSystemDerivedPullback (integralSystemRings l L) (integralSystemTransition l L) f :=
  integralComparisonSystemScalarPullback l E L ι f

private abbrev integralCompositionFiniteScalarIso (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι X ⋙ integralSystemReduction l L X ≅
      integralSystemReduction l E X ⋙ integralCompositionFiniteScalar l E L ι X :=
  integralSystemScalarIso l E L ι X

private theorem integralCompositionFiniteScalar_square {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralSystemReduction l L X).map (integralPullbackScalarComparison l E L ι f K).hom ≫
        (integralPullbackSystemIso l L f).hom.app
          ((sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
            E L ι Y).obj K) ≫
        (finiteSystemDerivedPullback (integralSystemRings l L)
          (integralSystemTransition l L) f).map
            ((integralCompositionFiniteScalarIso l E L ι Y).hom.app K) =
      (integralCompositionFiniteScalarIso l E L ι X).hom.app
          ((constructibleIntegralPullback l E f).obj K) ≫
        (integralCompositionFiniteScalar l E L ι X).map
          ((integralPullbackSystemIso l E f).hom.app K) ≫
        (integralCompositionFiniteScalarPullback l E L ι f).hom.app
          ((integralSystemReduction l E Y).obj K) :=
  integralPullbackSystemIso_scalar l E L ι f K

private theorem scalar_comp_naturality {C D D' B : Type*}
    [Category C] [Category D] [Category D'] [Category B]
    (F : C ⥤ D) (G : D ⥤ B) (F' : C ⥤ D') (G' : D' ⥤ B)
    (η : F ⋙ G ⟶ F' ⋙ G') {X Y : C} (f : X ⟶ Y) :
    G.map (F.map f) ≫ η.app Y = η.app X ≫ G'.map (F'.map f) :=
  η.naturality f

private theorem scalar_right_comp_naturality {C D B : Type*}
    [Category C] [Category D] [Category B]
    (F : C ⥤ B) (G : C ⥤ D) (H : D ⥤ B)
    (η : F ⟶ G ⋙ H) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ η.app Y = η.app X ≫ H.map (G.map f) :=
  η.naturality f

/-- Map a composite equation with its factors already expanded.
Source: functoriality. -/
private theorem scalar_map_three_eq_three {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B C' D' E' F' : C}
    {a : A ⟶ B} {b : B ⟶ C'} {c : C' ⟶ D'}
    {d : A ⟶ E'} {e : E' ⟶ F'} {f : F' ⟶ D'}
    (h : a ≫ b ≫ c = d ≫ e ≫ f) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e ≫ F.map f := by
  simpa only [Functor.map_comp] using congrArg F.map h

/-- Map a composite equation with its factors already expanded.
Source: functoriality. -/
private theorem scalar_map_three_eq_two {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B C' D' E' : C}
    {a : A ⟶ B} {b : B ⟶ C'} {c : C' ⟶ D'} {d : A ⟶ E'} {e : E' ⟶ D'}
    (h : a ≫ b ≫ c = d ≫ e) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e := by
  simpa only [Functor.map_comp] using congrArg F.map h

/-- Pasting of the scalar-composition diagram after mapping all of its edges into
one category. Source: elementary category theory. -/
private theorem scalar_composition_paste_mapped
    {D : Type*} [Category D]
    {O0 O1 O2 O3 O4 F0 F1 M1 M2 M3 N1 N2 N3 E0 E2 E3 E4 E5 : D}
    {x1 : O0 ⟶ O1} {x2 : O1 ⟶ O2} {x3 : O2 ⟶ O3} {t1 : O3 ⟶ M1}
    {bLk : M1 ⟶ M2} {pVk : M2 ⟶ M3} {b1 : O2 ⟶ N1} {sk : N1 ⟶ M1}
    {pW : N1 ⟶ N2} {HWbEk : N2 ⟶ N3} {gk : N3 ⟶ M3}
    {pZ1 : O1 ⟶ E2} {bEh : E2 ⟶ E3} {g1 : E3 ⟶ N2}
    {UEhbEk : E3 ⟶ E4} {g2 : E4 ⟶ N3}
    {pZ0 : O0 ⟶ E0} {cEr : E0 ⟶ E2} {bEhk : E0 ⟶ E5} {aE : E5 ⟶ E4}
    {ghk : E5 ⟶ F1} {aL2 : F1 ⟶ M3}
    {y1 : O0 ⟶ O4} {bLhk : O4 ⟶ F0} {q : F0 ⟶ F1} {aL1 : F0 ⟶ M2}
    {y2 : O4 ⟶ O3}
    (hN1 : x3 ≫ t1 = b1 ≫ sk)
    (hIIIk : sk ≫ bLk ≫ pVk = pW ≫ HWbEk ≫ gk)
    (hIIIh : x2 ≫ b1 ≫ pW = pZ1 ≫ bEh ≫ g1)
    (hNg : UEhbEk ≫ g2 = g1 ≫ HWbEk)
    (hNp : x1 ≫ pZ1 = pZ0 ≫ cEr)
    (hCE : cEr ≫ bEh ≫ UEhbEk = bEhk ≫ aE)
    {aE' : E5 ⟶ E4} {aL2' : F1 ⟶ M3}
    (hMix : aE' ≫ g2 ≫ gk = ghk ≫ aL2') (hE : aE = aE') (hL : aL2 = aL2')
    (hIIIhk : y1 ≫ bLhk ≫ q = pZ0 ≫ bEhk ≫ ghk)
    (hNa : q ≫ aL2 = aL1 ≫ pVk)
    (hCL : y2 ≫ t1 ≫ bLk = bLhk ≫ aL1) :
    x1 ≫ x2 ≫ x3 ≫ t1 ≫ bLk ≫ pVk = y1 ≫ y2 ≫ t1 ≫ bLk ≫ pVk := by
  subst hE hL
  rw [reassoc_of% hN1, hIIIk, reassoc_of% hIIIh, ← reassoc_of% hNg, reassoc_of% hNp,
    reassoc_of% hCE, hMix, ← reassoc_of% hIIIhk, hNa, ← reassoc_of% hCL]

/-- The pasting calculation behind integralPullbackComposition_scalar, with all
morphisms abstract. Source: elementary category theory. -/
private theorem scalar_composition_paste
    {D DE WL : Type*} [Category D] [Category DE] [Category WL]
    (U : WL ⥤ D) (H : DE ⥤ D)
    {O0 O1 O2 O3 O4 F0 F1 : D} {M1 M2 M3 N1 N2 N3 : WL} {E0 E2 E3 E4 E5 : DE}
    {x1 : O0 ⟶ O1} {x2 : O1 ⟶ O2} {x3 : O2 ⟶ O3} {t1 : O3 ⟶ U.obj M1}
    {bLk : M1 ⟶ M2} {pVk : M2 ⟶ M3} {b1 : O2 ⟶ U.obj N1} {sk : N1 ⟶ M1}
    {pW : N1 ⟶ N2} {HWbEk : N2 ⟶ N3} {gk : N3 ⟶ M3}
    {pZ1 : O1 ⟶ H.obj E2} {bEh : E2 ⟶ E3} {g1 : H.obj E3 ⟶ U.obj N2}
    {UEhbEk : E3 ⟶ E4} {g2 : H.obj E4 ⟶ U.obj N3}
    {pZ0 : O0 ⟶ H.obj E0} {cEr : E0 ⟶ E2} {bEhk : E0 ⟶ E5} {aE : E5 ⟶ E4}
    {ghk : H.obj E5 ⟶ F1} {aL2 : F1 ⟶ U.obj M3}
    {y1 : O0 ⟶ O4} {bLhk : O4 ⟶ F0} {q : F0 ⟶ F1} {aL1 : F0 ⟶ U.obj M2}
    {y2 : O4 ⟶ O3}
    (N1 : x3 ≫ t1 = b1 ≫ U.map sk)
    (IIIk : sk ≫ bLk ≫ pVk = pW ≫ HWbEk ≫ gk)
    (IIIh : x2 ≫ b1 ≫ U.map pW = pZ1 ≫ H.map bEh ≫ g1)
    (Ng : H.map UEhbEk ≫ g2 = g1 ≫ U.map HWbEk)
    (Np : x1 ≫ pZ1 = pZ0 ≫ H.map cEr)
    (CE : cEr ≫ bEh ≫ UEhbEk = bEhk ≫ aE)
    {aE' : E5 ⟶ E4} {aL2' : F1 ⟶ U.obj M3}
    (mix : H.map aE' ≫ g2 ≫ U.map gk = ghk ≫ aL2') (eE : aE = aE') (eL : aL2 = aL2')
    (IIIhk : y1 ≫ bLhk ≫ q = pZ0 ≫ H.map bEhk ≫ ghk)
    (Na : q ≫ aL2 = aL1 ≫ U.map pVk)
    (CL : y2 ≫ t1 ≫ U.map bLk = bLhk ≫ aL1) :
    x1 ≫ x2 ≫ x3 ≫ t1 ≫ U.map bLk ≫ U.map pVk =
      y1 ≫ y2 ≫ t1 ≫ U.map bLk ≫ U.map pVk := by
  have IIIk' := congrArg U.map IIIk
  have CE' := congrArg H.map CE
  simp only [Functor.map_comp] at IIIk' CE'
  exact scalar_composition_paste_mapped N1 IIIk' IIIh Ng Np CE' mix
    (congrArg H.map eE) eL IIIhk Na CL

private theorem integralComparisonSystemScalarPullback_finite_naturality
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    {M N : finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) Y}
    (a : M ⟶ N) :
    (integralCompositionFiniteScalar l E L ι X).map
        ((finiteSystemDerivedPullback (integralSystemRings l E)
          (integralSystemTransition l E) f).map a) ≫
        (integralCompositionFiniteScalarPullback l E L ι f).hom.app N =
      (integralCompositionFiniteScalarPullback l E L ι f).hom.app M ≫
        (finiteSystemDerivedPullback (integralSystemRings l L)
          (integralSystemTransition l L) f).map
            ((integralCompositionFiniteScalar l E L ι Y).map a) := by
  exact (integralCompositionFiniteScalarPullback l E L ι f).hom.naturality a

private theorem integralCompositionCategory_eq (X : Scheme.{u}) :
    finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) X =
      coefficientSequenceDerived l E X := by
  rfl

private theorem integralCompositionCategory_heq (X : Scheme.{u}) :
    HEq (inferInstance : Category
      (finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) X))
      (inferInstance : Category (coefficientSequenceDerived l E X)) := by
  exact HEq.rfl

private theorem integralCompositionPullback_heq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (finiteSystemDerivedPullback (integralSystemRings l E)
      (integralSystemTransition l E) f) (integralComparisonDerivedSequencePullback l E f) := by
  exact HEq.rfl

private theorem integralCompositionCompositor_heq {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    HEq (finiteSystemDerivedComposition (integralSystemRings l E)
      (integralSystemTransition l E) h k) (integralComparisonSystemComposition l E h k) := by
  exact heq_of_eq (finiteSystemDerivedComposition_eq_integralComparison l E h k)

/-- The scalar functor is unchanged by displaying its finite-system endpoints. -/
private theorem integralCompositionScalar_heq (X : Scheme.{u}) :
    HEq (integralCompositionFiniteScalar l E L ι X)
      (integralComparisonDerivedSequenceScalar l E L ι X) := by
  exact HEq.rfl

/-- The scalar/pullback comparison is unchanged by displaying its finite-system endpoints. -/
private theorem integralCompositionScalarPullback_heq {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :
    HEq (integralCompositionFiniteScalarPullback l E L ι f)
      (integralComparisonSystemScalarPullback l E L ι f) := by
  exact HEq.rfl

universe v₁ v₂ v₃ v₄ v₅ v₆ w₁ w₂ w₃ w₄ w₅ w₆ in
/-- Transport mixed coherence across identified presentations before taking components.
This keeps the coherence equation in its own categories throughout the comparison. -/
private theorem scalar_mixed_component_heq
    {EV EV' : Type w₁} [iEV : Category.{v₁} EV] [iEV' : Category.{v₁} EV']
    {EW EW' : Type w₂} [iEW : Category.{v₂} EW] [iEW' : Category.{v₂} EW']
    {EZ EZ' : Type w₃} [iEZ : Category.{v₃} EZ] [iEZ' : Category.{v₃} EZ']
    {LV LV' : Type w₄} [iLV : Category.{v₄} LV] [iLV' : Category.{v₄} LV']
    {LW LW' : Type w₅} [iLW : Category.{v₅} LW] [iLW' : Category.{v₅} LW']
    {LZ LZ' : Type w₆} [iLZ : Category.{v₆} LZ] [iLZ' : Category.{v₆} LZ']
    (eEV : EV = EV') (eiEV : HEq iEV iEV')
    (eEW : EW = EW') (eiEW : HEq iEW iEW')
    (eEZ : EZ = EZ') (eiEZ : HEq iEZ iEZ')
    (eLV : LV = LV') (eiLV : HEq iLV iLV')
    (eLW : LW = LW') (eiLW : HEq iLW iLW')
    (eLZ : LZ = LZ') (eiLZ : HEq iLZ iLZ')
    (UEk : EV ⥤ EW) (UEk' : EV' ⥤ EW') (eUEk : HEq UEk UEk')
    (UEh : EW ⥤ EZ) (UEh' : EW' ⥤ EZ') (eUEh : HEq UEh UEh')
    (UEhk : EV ⥤ EZ) (UEhk' : EV' ⥤ EZ') (eUEhk : HEq UEhk UEhk')
    (ULk : LV ⥤ LW) (ULk' : LV' ⥤ LW') (eULk : HEq ULk ULk')
    (ULh : LW ⥤ LZ) (ULh' : LW' ⥤ LZ') (eULh : HEq ULh ULh')
    (ULhk : LV ⥤ LZ) (ULhk' : LV' ⥤ LZ') (eULhk : HEq ULhk ULhk')
    (SV : EV ⥤ LV) (SV' : EV' ⥤ LV') (eSV : HEq SV SV')
    (SW : EW ⥤ LW) (SW' : EW' ⥤ LW') (eSW : HEq SW SW')
    (SZ : EZ ⥤ LZ) (SZ' : EZ' ⥤ LZ') (eSZ : HEq SZ SZ')
    (gh : UEh ⋙ SZ ≅ SW ⋙ ULh) (gh' : UEh' ⋙ SZ' ≅ SW' ⋙ ULh') (egh : HEq gh gh')
    (gk : UEk ⋙ SW ≅ SV ⋙ ULk) (gk' : UEk' ⋙ SW' ≅ SV' ⋙ ULk') (egk : HEq gk gk')
    (ghk : UEhk ⋙ SZ ≅ SV ⋙ ULhk) (ghk' : UEhk' ⋙ SZ' ≅ SV' ⋙ ULhk') (eghk : HEq ghk ghk')
    (aE : UEhk ≅ UEk ⋙ UEh) (aE' : UEhk' ≅ UEk' ⋙ UEh') (eaE : HEq aE aE')
    (aL : ULhk ≅ ULk ⋙ ULh) (aL' : ULhk' ≅ ULk' ⋙ ULh') (eaL : HEq aL aL')
    (mixed : Functor.whiskerRight aE'.hom SZ' ≫ Functor.whiskerLeft UEk' gh'.hom ≫
        Functor.whiskerRight gk'.hom ULh' = ghk'.hom ≫ Functor.whiskerLeft SV' aL'.hom)
    (M : EV) :
    SZ.map (aE.hom.app M) ≫ gh.hom.app (UEk.obj M) ≫ ULh.map (gk.hom.app M) =
      ghk.hom.app M ≫ aL.hom.app (SV.obj M) := by
  subst eEV eEW eEZ eLV eLW eLZ
  obtain rfl := eq_of_heq eiEV
  obtain rfl := eq_of_heq eiEW
  obtain rfl := eq_of_heq eiEZ
  obtain rfl := eq_of_heq eiLV
  obtain rfl := eq_of_heq eiLW
  obtain rfl := eq_of_heq eiLZ
  obtain rfl := eq_of_heq eUEk
  obtain rfl := eq_of_heq eUEh
  obtain rfl := eq_of_heq eUEhk
  obtain rfl := eq_of_heq eULk
  obtain rfl := eq_of_heq eULh
  obtain rfl := eq_of_heq eULhk
  obtain rfl := eq_of_heq eSV
  obtain rfl := eq_of_heq eSW
  obtain rfl := eq_of_heq eSZ
  obtain rfl := eq_of_heq egh
  obtain rfl := eq_of_heq egk
  obtain rfl := eq_of_heq eghk
  obtain rfl := eq_of_heq eaE
  obtain rfl := eq_of_heq eaL
  exact NatTrans.congr_app mixed M

private theorem integralCompositionFinite_mixed
    {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V)
    (M : finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) V) :
    (integralCompositionFiniteScalar l E L ι Z).map
        ((finiteSystemDerivedComposition (integralSystemRings l E)
          (integralSystemTransition l E) h k).hom.app M) ≫
      (integralCompositionFiniteScalarPullback l E L ι h).hom.app
        ((finiteSystemDerivedPullback (integralSystemRings l E)
          (integralSystemTransition l E) k).obj M) ≫
      (finiteSystemDerivedPullback (integralSystemRings l L)
        (integralSystemTransition l L) h).map
          ((integralCompositionFiniteScalarPullback l E L ι k).hom.app M) =
      (integralCompositionFiniteScalarPullback l E L ι (h ≫ k)).hom.app M ≫
        (finiteSystemDerivedComposition (integralSystemRings l L)
          (integralSystemTransition l L) h k).hom.app
          ((integralCompositionFiniteScalar l E L ι V).obj M) := by
  refine scalar_mixed_component_heq
    (integralCompositionCategory_eq l E V) (integralCompositionCategory_heq l E V)
    (integralCompositionCategory_eq l E W) (integralCompositionCategory_heq l E W)
    (integralCompositionCategory_eq l E Z) (integralCompositionCategory_heq l E Z)
    (integralCompositionCategory_eq l L V) (integralCompositionCategory_heq l L V)
    (integralCompositionCategory_eq l L W) (integralCompositionCategory_heq l L W)
    (integralCompositionCategory_eq l L Z) (integralCompositionCategory_heq l L Z)
    (finiteSystemDerivedPullback (integralSystemRings l E)
      (integralSystemTransition l E) k)
    (integralComparisonDerivedSequencePullback l E k)
    (integralCompositionPullback_heq l E k)
    (finiteSystemDerivedPullback (integralSystemRings l E)
      (integralSystemTransition l E) h)
    (integralComparisonDerivedSequencePullback l E h)
    (integralCompositionPullback_heq l E h)
    (finiteSystemDerivedPullback (integralSystemRings l E)
      (integralSystemTransition l E) (h ≫ k))
    (integralComparisonDerivedSequencePullback l E (h ≫ k))
    (integralCompositionPullback_heq l E (h ≫ k))
    (finiteSystemDerivedPullback (integralSystemRings l L)
      (integralSystemTransition l L) k)
    (integralComparisonDerivedSequencePullback l L k)
    (integralCompositionPullback_heq l L k)
    (finiteSystemDerivedPullback (integralSystemRings l L)
      (integralSystemTransition l L) h)
    (integralComparisonDerivedSequencePullback l L h)
    (integralCompositionPullback_heq l L h)
    (finiteSystemDerivedPullback (integralSystemRings l L)
      (integralSystemTransition l L) (h ≫ k))
    (integralComparisonDerivedSequencePullback l L (h ≫ k))
    (integralCompositionPullback_heq l L (h ≫ k))
    (integralCompositionFiniteScalar l E L ι V)
    (integralComparisonDerivedSequenceScalar l E L ι V)
    (integralCompositionScalar_heq l E L ι V)
    (integralCompositionFiniteScalar l E L ι W)
    (integralComparisonDerivedSequenceScalar l E L ι W)
    (integralCompositionScalar_heq l E L ι W)
    (integralCompositionFiniteScalar l E L ι Z)
    (integralComparisonDerivedSequenceScalar l E L ι Z)
    (integralCompositionScalar_heq l E L ι Z)
    (integralCompositionFiniteScalarPullback l E L ι h)
    (integralComparisonSystemScalarPullback l E L ι h)
    (integralCompositionScalarPullback_heq l E L ι h)
    (integralCompositionFiniteScalarPullback l E L ι k)
    (integralComparisonSystemScalarPullback l E L ι k)
    (integralCompositionScalarPullback_heq l E L ι k)
    (integralCompositionFiniteScalarPullback l E L ι (h ≫ k))
    (integralComparisonSystemScalarPullback l E L ι (h ≫ k))
    (integralCompositionScalarPullback_heq l E L ι (h ≫ k))
    (finiteSystemDerivedComposition (integralSystemRings l E)
      (integralSystemTransition l E) h k)
    (integralComparisonSystemComposition l E h k)
    (integralCompositionCompositor_heq l E h k)
    (finiteSystemDerivedComposition (integralSystemRings l L)
      (integralSystemTransition l L) h k)
    (integralComparisonSystemComposition l L h k)
    (integralCompositionCompositor_heq l L h k)
    ((integralQuotientMixedCoherence.{u, u} l).derived_mixed E L ι h k) M

-- Mixed coherence is transported once between the two presentations of reduction systems.
/-- Scalar extension carries the integral pullback compositor at E to the one at L.
Source: Stacks 06YY, 07A4, 0941, 0D6D; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-composition-scalar).
Proof: apply the faithful coherent reduction at L and cancel the invertible comparison
beta_h (U_h beta_k)(U_h U_k p). Naturality of beta_h, the pullback/scalar square for k and
h, naturality of the whole-system scalar/pullback comparison and of p, the system clause
of integralPullbackComposition at E, whole-system mixed coherence, the pullback/scalar
square for h k, naturality of the finite-system composition and the system clause at L
transform one side into the other. -/
theorem integralPullbackComposition_scalar {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι Z).map (((integralPullbackComposition l E).choose h k).hom.app K) ≫
      (integralPullbackScalarComparison l E L ι h
        ((constructibleIntegralPullback l E k).obj K)).hom ≫
      (constructibleIntegralPullback l L h).map
        (integralPullbackScalarComparison l E L ι k K).hom =
    (integralPullbackScalarComparison l E L ι (h ≫ k) K).hom ≫
      ((integralPullbackComposition l L).choose h k).hom.app
        ((sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι V).obj K) := by
  have : (integralSystemReduction l L Z).Faithful :=
    (integralSystemReduction_fullyFaithful l L Z).2
  apply (integralSystemReduction l L Z).map_injective
  let SV := sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
    E L ι V
  let UL {A B : Scheme.{u}} (f : A ⟶ B) :=
    finiteSystemDerivedPullback (integralSystemRings l L) (integralSystemTransition l L) f
  let T := (integralPullbackSystemIso l L h).app
      ((constructibleIntegralPullback l L k).obj (SV.obj K)) ≪≫
    (UL h).mapIso ((integralPullbackSystemIso l L k).app (SV.obj K)) ≪≫
    (UL h).mapIso ((UL k).mapIso ((integralCompositionFiniteScalarIso l E L ι V).app K))
  apply (cancel_mono T.hom).1
  have N1 := scalar_comp_naturality
    (constructibleIntegralPullback l L h) (integralSystemReduction l L Z)
    (integralSystemReduction l L W) (UL h) (integralPullbackSystemIso l L h).hom
    (integralPullbackScalarComparison l E L ι k K).hom
  have IIIk := integralCompositionFiniteScalar_square l E L ι k K
  have IIIh := integralCompositionFiniteScalar_square l E L ι h
    ((constructibleIntegralPullback l E k).obj K)
  have Ng := integralComparisonSystemScalarPullback_finite_naturality l E L ι h
    ((integralPullbackSystemIso l E k).hom.app K)
  have Np := scalar_comp_naturality
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι Z) (integralSystemReduction l L Z)
    (integralSystemReduction l E Z) (integralCompositionFiniteScalar l E L ι Z)
    (integralCompositionFiniteScalarIso l E L ι Z).hom
    (((integralPullbackComposition l E).choose h k).hom.app K)
  have CE := (integralPullbackComposition l E).choose_spec.2.2 h k K
  simp only [integralPullbackSystemComparison_choose] at CE
  have mix := integralCompositionFinite_mixed l E L ι h k
    ((integralSystemReduction l E V).obj K)
  have IIIhk := integralCompositionFiniteScalar_square l E L ι (h ≫ k) K
  have Na := scalar_right_comp_naturality (UL (h ≫ k)) (UL k) (UL h)
    (finiteSystemDerivedComposition (integralSystemRings l L)
      (integralSystemTransition l L) h k).hom
    ((integralCompositionFiniteScalarIso l E L ι V).hom.app K)
  have CL := (integralPullbackComposition l L).choose_spec.2.2 h k (SV.obj K)
  simp only [integralPullbackSystemComparison_choose] at CL
  simp only [T, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  have IIIk' := scalar_map_three_eq_three (UL h) IIIk
  have CE' := scalar_map_three_eq_two
    (C := finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) Z)
    (integralCompositionFiniteScalar l E L ι Z) CE
  exact scalar_composition_paste_mapped
    (D := finiteSystemDerived (integralSystemRings l L) (integralSystemTransition l L) Z)
    (hN1 := N1) (hIIIk := IIIk') (hIIIh := IIIh)
    (hNg := Ng) (hNp := Np) (hCE := CE') (hMix := mix) (hE := rfl) (hL := rfl)
    (hIIIhk := IIIhk) (hNa := Na) (hCL := CL)

end SystemScalar

end WeilConjectures
