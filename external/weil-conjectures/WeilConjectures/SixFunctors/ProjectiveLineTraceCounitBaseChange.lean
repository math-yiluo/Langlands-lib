/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProjectiveLineTraceModel
import WeilConjectures.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback
import WeilConjectures.SixFunctors.ProjectiveLinePresentedTraceExchange
import WeilConjectures.SixFunctors.ProperOrderedProjectionExchange

/-! # Pullback of the explicit inverse-projection trace counit

This equality concerns constructed trace maps and uses no exceptional right adjoints.
-/

@[expose] public section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedTensor rightDerivedLowerShriek
  rightDerivedLowerShriekBaseChangeMap rightDerivedLowerShriekIsoRightDerivedLowerStar

private theorem regroupFour
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ O₄ O₅ : C}
    {a : O₀ ⟶ O₁} {b : O₁ ⟶ O₂} {c : O₂ ⟶ O₃} {d : O₃ ⟶ O₄}
    {e : O₄ ⟶ O₅} {r : O₀ ⟶ O₅}
    (h : a ≫ b ≫ c ≫ d ≫ e = r) : (a ≫ b ≫ c ≫ d) ≫ e = r := by
  simpa -implicitDefEqProofs only [Category.assoc] using h

private theorem inverseUnitSquare
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ : C}
    (i : O₀ ≅ O₁) (j : O₃ ≅ O₁) (a : O₀ ⟶ O₂) (b : O₂ ⟶ O₃)
    (h : i.inv ≫ a ≫ b = j.inv) : a ≫ b ≫ j.hom = i.hom := by
  apply (cancel_epi i.inv).1
  rw [reassoc_of% h, j.inv_hom_id, i.inv_hom_id]

private theorem tensorTracePasting
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (S : C ⥤ C) (T : D ⥤ D)
    {B U K : C} {B' U' : D} (b : F.obj B ⟶ B')
    (τ : B ⟶ U) (τ' : B' ⟶ U') (u : F.obj U ⟶ U')
    (a : F.obj (S.obj B) ⟶ T.obj (F.obj B))
    (aU : F.obj (S.obj U) ⟶ T.obj (F.obj U))
    (r : S.obj U ⟶ K) (r' : T.obj U' ⟶ F.obj K)
    (tt : S.obj B ⟶ K) (tt' : T.obj B' ⟶ F.obj K)
    (hτ : b ≫ τ' = F.map τ ≫ u)
    (hn : F.map (S.map τ) ≫ aU = a ≫ T.map (F.map τ))
    (hr : aU ≫ T.map u ≫ r' = F.map r)
    (htt : tt = S.map τ ≫ r) (htt' : tt' = T.map τ' ≫ r') :
    a ≫ T.map b ≫ tt' = F.map tt := by
  have hm : T.map b ≫ T.map τ' = T.map (F.map τ) ≫ T.map u :=
    (T.map_comp b τ').symm.trans
      ((T.congr_map hτ).trans (T.map_comp (F.map τ) u))
  rw [htt, htt']
  simp -implicitDefEqProofs only [Functor.map_comp]
  rw [reassoc_of% hm, ← reassoc_of% hn, hr]

private theorem projectionCounitCancellation
    {C : Type*} [Category C] {O₀ O₁ O₂ O₃ : C}
    (p : O₀ ≅ O₁) (c : O₂ ≅ O₁) (τ : O₀ ⟶ O₃) :
    (p.hom ≫ c.inv) ≫ (c.hom ≫ p.inv ≫ τ) = τ := by
  simp -implicitDefEqProofs only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

private theorem counitExchange
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {O₀ O₁ O₂ : C} (P : O₀ ⟶ O₁) [IsIso P]
    {D₀ D₁ D₂ D₃ : D} (b : F.obj O₁ ⟶ D₀) (c : D₀ ⟶ D₁)
    (e : O₁ ⟶ O₂) (e' : D₁ ⟶ F.obj O₂)
    (a : F.obj O₀ ⟶ D₂) (d : D₂ ⟶ D₃) (P' : D₃ ⟶ D₁)
    (tt : O₀ ⟶ O₂) (tt' : D₃ ⟶ F.obj O₂)
    (hp : F.map P ≫ b ≫ c = a ≫ d ≫ P')
    (ht : a ≫ d ≫ tt' = F.map tt)
    (he : P ≫ e = tt) (he' : P' ≫ e' = tt') :
    b ≫ c ≫ e' = F.map e := by
  apply (cancel_epi (F.map P)).1
  calc
    _ = a ≫ d ≫ P' ≫ e' := by rw [reassoc_of% hp]
    _ = F.map tt := by rw [he', ht]
    _ = F.map (P ≫ e) := F.congr_map he.symm
    _ = F.map P ≫ F.map e := F.map_comp P e

private theorem tensorTrace_exchange
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    {B : DerivedCategoryModule A Y} {B' : DerivedCategoryModule A Y'}
    (b : (ordinaryFinitePullback A g).obj B ⟶ B')
    (τ : B ⟶ ordinaryFiniteUnit A Y) (τ' : B' ⟶ ordinaryFiniteUnit A Y')
    (hτ : b ≫ τ' = (ordinaryFinitePullback A g).map τ ≫
      (ordinaryFiniteUnitPullback A g).hom) (K : DerivedCategoryModule A Y) :
    (ordinaryFiniteTensorPullback A g K B).hom ≫
      ((ordinaryFiniteTensor A Y').obj ((ordinaryFinitePullback A g).obj K)).map b ≫
      (ordinaryFiniteTensorTrace A Y' τ').app ((ordinaryFinitePullback A g).obj K) =
    (ordinaryFinitePullback A g).map ((ordinaryFiniteTensorTrace A Y τ).app K) := by
  let F := ordinaryFinitePullback A g
  let T := (ordinaryFiniteTensor A Y').obj (F.obj K)
  have hu := (finiteTwistDerivedEvaluation_pullback A N hN hA t g hY).2 K
  have hr : (ordinaryFiniteTensorPullback A g K (ordinaryFiniteUnit A Y)).hom ≫
      T.map (ordinaryFiniteUnitPullback A g).hom ≫
      (derivedTensorSingleUnitIso (F.obj K)).hom =
      F.map (derivedTensorSingleUnitIso K).hom :=
    inverseUnitSquare (F.mapIso (derivedTensorSingleUnitIso K))
      (derivedTensorSingleUnitIso (F.obj K)) _ _ hu
  have hn := leftDerivedUpperStarTensorIso_hom_naturality_right
    (A := ModuleCat.{u + 1} A) g K τ
  exact tensorTracePasting F ((ordinaryFiniteTensor A Y).obj K) T b τ τ'
    (ordinaryFiniteUnitPullback A g).hom
    (ordinaryFiniteTensorPullback A g K B).hom
    (ordinaryFiniteTensorPullback A g K (ordinaryFiniteUnit A Y)).hom
    (derivedTensorSingleUnitIso K).hom (derivedTensorSingleUnitIso (F.obj K)).hom
    ((ordinaryFiniteTensorTrace A Y τ).app K)
    ((ordinaryFiniteTensorTrace A Y' τ').app (F.obj K)) hτ hn hr
    (ordinaryFiniteTensorTrace_app A Y τ K)
    (ordinaryFiniteTensorTrace_app A Y' τ' (F.obj K))

private theorem projection_traceCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (L : DerivedCategoryModule A X)
    (τ : (ordinaryFinitePushforward A q).obj L ⟶ ordinaryFiniteUnit A Y)
    (K : DerivedCategoryModule A Y) :
    (ordinaryFiniteProjection A q L K ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).inv.app
            ((ordinaryFiniteTwistedPullback A q L).obj K)) ≫
      (finiteP1TraceCounit A q L τ).app K = (ordinaryFiniteTensorTrace A Y τ).app K := by
  have := isIso_finiteP1Projection A q L
  let p := asIso (ordinaryFiniteProjectionNatTrans A q L)
  let c := Functor.isoWhiskerLeft (ordinaryFiniteTwistedPullback A q L)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q)
  unfold finiteP1TraceCounit
  exact NatTrans.congr_app
    (projectionCounitCancellation p c (ordinaryFiniteTensorTrace A Y τ)) K

private theorem counit_of_trace_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (hY : IsUnit (N : Γ(Y, ⊤)))
    (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule A X')
    (l : (ordinaryFinitePullback A g').obj L ≅ L')
    (τ : (ordinaryFinitePushforward A q).obj L ⟶ ordinaryFiniteUnit A Y)
    (τ' : (ordinaryFinitePushforward A q').obj L' ⟶ ordinaryFiniteUnit A Y')
    (htrace : (ordinaryFinitePullback A g).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).inv.app L) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app L ≫
      (R(q')_![ModuleCat.{u + 1} A]).map l.hom ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) q').hom.app L' ≫ τ' =
      (ordinaryFinitePullback A g).map τ ≫ (ordinaryFiniteUnitPullback A g).hom)
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriekBaseChangeMap A sq).app
        ((ordinaryFiniteTwistedPullback A q L).obj K) ≫
      (R(q')_![ModuleCat.{u + 1} A]).map
        (ordinaryFiniteTwistedPullbackComparison A q q' g g' L L' K
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K) l).hom ≫
      (finiteP1TraceCounit A q' L' τ').app ((ordinaryFinitePullback A g).obj K) =
    (ordinaryFinitePullback A g).map ((finiteP1TraceCounit A q L τ).app K) := by
  let E := (ordinaryFinitePullback A g).map
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) q).inv.app L) ≫
    (rightDerivedLowerShriekBaseChangeMap A sq).app L ≫
    (R(q')_![ModuleCat.{u + 1} A]).map l.hom ≫
    (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q').hom.app L'
  let P := ordinaryFiniteProjection A q L K ≫
    (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q).inv.app ((ordinaryFiniteTwistedPullback A q L).obj K)
  let P' := ordinaryFiniteProjection A q' L' ((ordinaryFinitePullback A g).obj K) ≫
    (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) q').inv.app
        ((ordinaryFiniteTwistedPullback A q' L').obj ((ordinaryFinitePullback A g).obj K))
  have hE := regroupFour htrace
  have ht := tensorTrace_exchange A N hN hA t g hY E τ τ' hE K
  have hp := properOrderedProjection_exchange A sq L L' l K
  have := isIso_finiteP1Projection A q L
  have : IsIso (ordinaryFiniteProjection A q L K) :=
    show IsIso ((ordinaryFiniteProjectionNatTrans A q L).app K) from inferInstance
  have : IsIso P :=
    IsIso.comp_isIso' (show IsIso (ordinaryFiniteProjection A q L K) from inferInstance)
      (NatIso.inv_app_isIso
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q)
        ((ordinaryFiniteTwistedPullback A q L).obj K))
  exact counitExchange (ordinaryFinitePullback A g) P
    ((rightDerivedLowerShriekBaseChangeMap A sq).app
      ((ordinaryFiniteTwistedPullback A q L).obj K))
    ((R(q')_![ModuleCat.{u + 1} A]).map (ordinaryFiniteTwistedPullbackComparison A q q' g g' L L' K
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K) l).hom)
    ((finiteP1TraceCounit A q L τ).app K)
    ((finiteP1TraceCounit A q' L' τ').app ((ordinaryFinitePullback A g).obj K))
    (ordinaryFiniteTensorPullback A g K ((ordinaryFinitePushforward A q).obj L)).hom
    (((ordinaryFiniteTensor A Y').obj ((ordinaryFinitePullback A g).obj K)).map E) P'
    ((ordinaryFiniteTensorTrace A Y τ).app K)
    ((ordinaryFiniteTensorTrace A Y' τ').app ((ordinaryFinitePullback A g).obj K)) hp ht
    (projection_traceCounit A q L τ K)
    (projection_traceCounit A q' L' τ' ((ordinaryFinitePullback A g).obj K))

-- Keep the exchange and counits as natural transformations until taking components.
-- This preserves the composite-functor object expressions of their public interfaces.
private theorem counit_of_trace_exchange_transport_ordinary
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (hY : IsUnit (N : Γ(Y, ⊤)))
    (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule A X')
    (l : (ordinaryFinitePullback A g').obj L ≅ L')
    (τ : (ordinaryFinitePushforward A q).obj L ⟶ ordinaryFiniteUnit A Y)
    (τ' : (ordinaryFinitePushforward A q').obj L' ⟶ ordinaryFiniteUnit A Y')
    (htrace : (ordinaryFinitePullback A g).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).inv.app L) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app L ≫
      (R(q')_![ModuleCat.{u + 1} A]).map l.hom ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) q').hom.app L' ≫ τ' =
      (ordinaryFinitePullback A g).map τ ≫ (ordinaryFiniteUnitPullback A g).hom)
    (K : DerivedCategoryModule A Y)
    (F : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A Y')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A X')
    (hF : F = ordinaryFinitePullback A g) (hG : G = ordinaryFinitePullback A g')
    (β : R(q)_![ModuleCat.{u + 1} A] ⋙ F ⟶ G ⋙ R(q')_![ModuleCat.{u + 1} A])
    (c : G.obj ((ordinaryFiniteTwistedPullback A q L).obj K) ≅
      (ordinaryFiniteTwistedPullback A q' L').obj (F.obj K))
    (hb : HEq β (rightDerivedLowerShriekBaseChangeMap A sq))
    (hc : HEq c (ordinaryFiniteTwistedPullbackComparison A q q' g g' L L' K
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K) l))
    (ε : ordinaryFiniteTwistedPullback A q L ⋙ R(q)_![ModuleCat.{u + 1} A] ⟶
      𝟭 (DerivedCategoryModule A Y))
    (ε' : ordinaryFiniteTwistedPullback A q' L' ⋙ R(q')_![ModuleCat.{u + 1} A] ⟶
      𝟭 (DerivedCategoryModule A Y'))
    (hε : ε = finiteP1TraceCounit A q L τ)
    (hε' : ε' = finiteP1TraceCounit A q' L' τ') :
    β.app ((ordinaryFiniteTwistedPullback A q L).obj K) ≫
      (R(q')_![ModuleCat.{u + 1} A]).map c.hom ≫ ε'.app (F.obj K) =
      F.map (ε.app K) := by
  subst F G ε ε'
  have hb' := eq_of_heq hb
  have hc' := eq_of_heq hc
  subst β c
  exact counit_of_trace_exchange A N hN hA t sq hY L L' l τ τ' htrace K

-- Convert category aliases while F and G are abstract. Specializing first makes the
-- kernel unfold the derived pullback when comparing its map expressions.
private theorem counit_of_trace_exchange_transport
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q'] (hY : IsUnit (N : Γ(Y, ⊤)))
    (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule A X')
    (l : (ordinaryFinitePullback A g').obj L ≅ L')
    (τ : (ordinaryFinitePushforward A q).obj L ⟶ ordinaryFiniteUnit A Y)
    (τ' : (ordinaryFinitePushforward A q').obj L' ⟶ ordinaryFiniteUnit A Y')
    (htrace : (ordinaryFinitePullback A g).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).inv.app L) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app L ≫
      (R(q')_![ModuleCat.{u + 1} A]).map l.hom ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) q').hom.app L' ≫ τ' =
      (ordinaryFinitePullback A g).map τ ≫ (ordinaryFiniteUnitPullback A g).hom)
    (K : DerivedCategoryModule A Y)
    (F : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : F = ordinaryFinitePullback A g) (hG : G = ordinaryFinitePullback A g')
    (β : R(q)_![ModuleCat.{u + 1} A] ⋙ F ⟶ G ⋙ R(q')_![ModuleCat.{u + 1} A])
    (c : G.obj ((ordinaryFiniteTwistedPullback A q L).obj K) ≅
      (ordinaryFiniteTwistedPullback A q' L').obj (F.obj K))
    (hb : HEq β (rightDerivedLowerShriekBaseChangeMap A sq))
    (hc : HEq c (ordinaryFiniteTwistedPullbackComparison A q q' g g' L L' K
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K) l))
    (ε : ordinaryFiniteTwistedPullback A q L ⋙ R(q)_![ModuleCat.{u + 1} A] ⟶
      𝟭 (DerivedCategoryModule A Y))
    (ε' : ordinaryFiniteTwistedPullback A q' L' ⋙ R(q')_![ModuleCat.{u + 1} A] ⟶
      𝟭 (DerivedCategoryModule A Y'))
    (hε : ε = finiteP1TraceCounit A q L τ)
    (hε' : ε' = finiteP1TraceCounit A q' L' τ') :
    β.app ((ordinaryFiniteTwistedPullback A q L).obj K) ≫
      (R(q')_![ModuleCat.{u + 1} A]).map c.hom ≫ ε'.app (F.obj K) =
      F.map (ε.app K) := by
  have h := counit_of_trace_exchange_transport_ordinary A N hN hA t sq hY
    L L' l τ τ' htrace K F G hF hG β c hb hc ε ε' hε hε'
  exact h

/-- Pullback preserves the constructed projective-line counit as an actual morphism.
Source: blueprint sec-six-functors-basics/sk-prop-sf-cbc/
prop-asd-smooth-base-change.proof.md, second paragraph, trace and projection squares;
sk-prop-geo-p1-adjunction/det-sp-p1-adjunction.proof.md, counit square.
(auxiliary; not a blueprint node)

Proof: first take the standard projective-space square. The supplied splitting
base-change property gives the trace square by its second clause. The ordered proper
projection commutes with exchange: conjugate the usual right-coefficient projection
square by tensor symmetries. Naturality of the projection in the finite-line comparison
then gives the square with the canonical twisted inverse-image comparison. Invert the
projection isomorphisms, append the trace square and the inverse-image unit constraint,
and cancel the proper direct-image comparisons. This is the displayed equation for
the constructed counits. For a general presentation, the pullback universal property
identifies its square with the standard one. The trace transport uses the adjunction
unit of the presentation isomorphism and derived composition; exchange pasting and
composition of the projection maps transport the standard equality to this square.
The compatibility of the two presentations with the horizontal morphism
identifies this transport with the specified twist comparison, using functoriality
of the normalized line comparisons. Proper coincidence respects exchange, giving
the stated compact-support exchange. All identities are natural-transformation
identities on unbounded categories, without detection of derived arrows by stalks.
Identity pullback, zero coefficients and the empty base cause no exception. -/
theorem presentedFiniteP1Counit_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' q' q g)
    [IsProper q] [IsProper q'] [HasCompactification q] [HasCompactification q']
    [QuasiCompact q']
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (e' : X' ≅ ProjectiveLine Y') (w' : e'.hom ≫ (ProjectiveLine Y' ↘ Y') = q')
    (we : e'.hom ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) g = g' ≫ e.hom)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hY' : IsUnit (N : Γ(Y', ⊤)))
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriekBaseChangeMap A sq).app
        ((ordinaryFiniteTwistedPullback A q
          ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)).obj K) ≫
      (R(q')_![ModuleCat.{u + 1} A]).map
        (finiteP1TwistedPullbackComparison A N hA t sq hY K).hom ≫
      (presentedFiniteP1Counit A N hA t q' e' w' hY' (d Y' hY')).app
        ((L((g)^*[ModuleCat.{u + 1} A])).obj K) =
    (L((g)^*[ModuleCat.{u + 1} A])).map
      ((presentedFiniteP1Counit A N hA t q e w hY (d Y hY)).app K) := by
  exact counit_of_trace_exchange_transport A N hN hA t sq hY
    ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)
    ((ordinaryFiniteLine A N hA X')⟦(2 : ℤ)⟧)
    (ordinaryFiniteShiftedLinePullback A N hA t g'
      (finiteP1_unitOnPullback N q hY))
    (presentedFiniteP1Trace A N hA t q e w hY (d Y hY))
    (presentedFiniteP1Trace A N hA t q' e' w' hY' (d Y' hY'))
    (presentedFiniteP1Trace_exchange A N hA t d hbc sq e w e' w' we hY hY') K
    (L((g)^*[ModuleCat.{u + 1} A])) (L((g')^*[ModuleCat.{u + 1} A])) rfl rfl
    (rightDerivedLowerShriekBaseChangeMap A sq)
    (finiteP1TwistedPullbackComparison A N hA t sq hY K) HEq.rfl HEq.rfl
    (presentedFiniteP1Counit A N hA t q e w hY (d Y hY))
    (presentedFiniteP1Counit A N hA t q' e' w' hY' (d Y' hY')) rfl rfl

end AlgebraicGeometry.Etale
