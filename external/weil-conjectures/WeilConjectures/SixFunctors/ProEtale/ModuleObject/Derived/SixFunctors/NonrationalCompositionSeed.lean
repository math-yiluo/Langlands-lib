/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.Compactification.Dense
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import Mathlib.CategoryTheory.Adjunction.CompositionIso
/-!
# One compactification model for nonrational lower-shriek composition

Source: blueprint main-20261015, sk-thm-sf-comp-composition.proof.md,
"The composition isomorphism" (blueprint: lem-sfb-nonrational-composition-seed).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private noncomputable def liftRingMap (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Profinite.continuousMapRingSheaf.{u} A ⟶
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ULift.ringEquiv : ULift.{u} A ≃+* A).symm.toRingHom.compLeftContinuous
            S.unop continuous_uliftUp).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩
private noncomputable def downRingMap (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Profinite.continuousCoefficientRingSheaf (ULift.{u} A) ⟶
      Profinite.continuousMapRingSheaf.{u} A :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom.compLeftContinuous
            S.unop continuous_uliftDown).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩
private noncomputable def liftRingIso (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) where
  hom := liftRingMap A
  inv := downRingMap A
  hom_inv_id := by ext S a; rfl
  inv_hom_id := by ext S a; rfl
private noncomputable def liftMonIso (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} A)) :=
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftRingIso A)
  have : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (liftRingIso A).hom))
  Mon.mkIso' e

private theorem normalizedIso_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R) [IsIso adj.unit]
    (T T' : C ⥤ D) (G : C ⥤ E) (δ : G ⋙ R ⟶ T') (β : T ≅ T')
    (e : ∀ X, L.obj (T.obj X) ≅ G.obj X)
    (he : ∀ X, adj.homEquiv _ _ (e X).hom ≫ δ.app X = β.hom.app X) :
    ∀ {X Y : C} (v : X ⟶ Y),
      L.map (T.map v) ≫ (e Y).hom = (e X).hom ≫ G.map v := by
  intro X Y v
  have hi (Z : C) : IsIso (δ.app Z) := by
    have h : IsIso (adj.homEquiv _ _ (e Z).hom) := by
      rw [Adjunction.homEquiv_unit]
      infer_instance
    have hc : IsIso (adj.homEquiv _ _ (e Z).hom ≫ δ.app Z) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left (adj.homEquiv _ _ (e Z).hom) (δ.app Z)
  have := hi Y
  apply (adj.homEquiv _ _).injective
  apply (cancel_mono (δ.app Y)).1
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  rw [Category.assoc, he, Category.assoc]
  change T.map v ≫ β.hom.app Y =
    adj.homEquiv _ _ (e X).hom ≫ (G ⋙ R).map v ≫ δ.app Y
  rw [δ.naturality, ← Category.assoc, he]
  exact β.hom.naturality v

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def interchangeRestrictionNatTrans
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Ybar : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Ybar)
    [IsOpenImmersion i] (c : Compactification.BoundaryCompactification (p ≫ i)) :
    (lowerStar Λ c.obj.obj.g).rightDerivedFunctor ⋙ (upperStar Λ i).mapDerivedCategory ⟶
      (upperStar Λ c.obj.obj.i).mapDerivedCategory ⋙ (lowerStar Λ p).rightDerivedFunctor :=
  (mateEquiv
    ((derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g))
    ((derivedUpperStarLowerStarAdjunction Λ p).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory Λ p))
    (TwoSquare.mk _ _ _ _ (compositionInterchangePullback Λ p i c).hom))

set_option backward.isDefEq.respectTransparency false in
private theorem interchangeRestrictionNatTrans_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Ybar : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Ybar)
    [IsOpenImmersion i] (c : Compactification.BoundaryCompactification (p ≫ i))
    (B : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology c.obj.obj.Z) Ab.{u + 1})
      (condensedRingObj Λ c.obj.obj.Z))) :
    (interchangeRestrictionNatTrans Λ p i c).app B =
      compositionInterchangeRestriction Λ p i c B := by
  simp [interchangeRestrictionNatTrans, compositionInterchangeRestriction,
    mateEquiv, Adjunction.homEquiv_unit]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A composition isomorphism exists for one triple of compactifications. No comparison
with other triples is asserted here. The preservation arguments only type the restrictions.

Source: blueprint main-20261015, sk-thm-sf-comp-composition.proof.md,
"The composition isomorphism" (blueprint: lem-sfb-nonrational-composition-seed).

Proof: Choose dense compactifications f = pj and g = qi by Nagata, then compactify ip as ru.
The pair (u ∘ j, q ∘ r) compactifies g ∘ f: open immersions and proper maps compose,
and quasi-compactness of the open follows from finite type. Extension by zero along j preserves
the localizing
closure. Proper/open interchange gives the unique map i! Rp* A → Rr* u! A restricting to the
identity, invertible for A in that closure. Its normalization and the open adjunction imply
naturality: the two composites associated to A → B have the same open adjoint. Apply this to
A = j! K and apply Rq*. Compose the derived proper-direct-image compositor with the open
extension compositor (the latter comes from uniqueness of left adjoints to the composite
pullback). This yields Rp*j! followed by Rq*i! isomorphic to R(q ∘ r)*(u ∘ j)!. The supplied
preservation proofs place the endpoints in the full localizing subcategory, whose fullness
lifts this ambient natural isomorphism. There is no compatibility claim to prove in this
lemma; transport by the cocycle supplies that part in the parent. -/
theorem exists_nonrationalLocalizingLowerShriekCompositionSeed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (_hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (hf : ∀ (c : Compactification.BoundaryCompactification f)
          (K : DerivedCategory (CategoryTheory.Mod
            (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
          localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hg : ∀ (c : Compactification.BoundaryCompactification g)
          (K : DerivedCategory (CategoryTheory.Mod
            (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))),
          localizingClosureProEtale Λ Y K → localizingClosureProEtale Λ Z
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hgf : ∀ (c : Compactification.BoundaryCompactification (f ≫ g))
          (K : DerivedCategory (CategoryTheory.Mod
            (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
          localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Z
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)) :
    ∃ (cf : Compactification.BoundaryCompactification f)
      (cg : Compactification.BoundaryCompactification g)
      (cgf : Compactification.BoundaryCompactification (f ≫ g)),
      Nonempty (localizingLowerShriek Λ cf.obj.obj (hf cf) ⋙
          localizingLowerShriek Λ cg.obj.obj (hg cg) ≅
        localizingLowerShriek Λ cgf.obj.obj (hgf cgf))  := by
  classical
  have hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases _hΛ with h | h | ⟨E, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩))))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  let : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let cf := denseCompactification f
  let cg := denseCompactification g
  let : CompactSpace cg.Z := QuasiCompact.compactSpace_of_compactSpace (cg.Z ↘ Spec (.of k))
  let : QuasiSeparatedSpace cg.Z :=
    quasiSeparatedSpace_of_quasiSeparated (cg.Z ↘ Spec (.of k))
  let : CompactSpace cf.Z :=
    QuasiCompact.compactSpace_of_compactSpace (cf.Z ↘ Spec (.of k))
  let : QuasiSeparatedSpace cf.Z :=
    quasiSeparatedSpace_of_quasiSeparated (cf.Z ↘ Spec (.of k))
  let : QuasiCompact cg.i := quasiCompact_of_compactSpace _
  let cr := denseCompactification (cf.g ≫ cg.i)
  let : QuasiCompact cf.i := quasiCompact_of_compactSpace _
  let : QuasiSeparatedSpace cr.Z :=
    quasiSeparatedSpace_of_quasiSeparated (cr.Z ↘ Spec (.of k))
  let : QuasiCompact cr.i := quasiCompact_of_compactSpace _
  let : IsSchemeTheoreticallyDominant cr.i := denseCompactification_isDense _
  let bc : Compactification.BoundaryCompactification (cf.g ≫ cg.i) := ⟨⟨cr, inferInstance⟩⟩
  have inter := properOpenInterchange Λ cf.g cg.i bc ℓ k
  have hcoef :
      (∃ (A : Type u) (_ : CommRing A) (_ : Finite A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        (∃ n : ℕ, (ℓ ^ n : A) = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
              (Profinite.padicSubfieldCondensedRing ℓ E.1)))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases _hΛ with ⟨A, hA, htop, hdisc, hring, hfin, ⟨n, hn⟩, ⟨e⟩⟩ | h | ⟨E, h⟩
    · let := hA
      let := htop
      let := hdisc
      let := hring
      let := hfin
      apply Or.inl
      refine ⟨ULift.{u} A, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, ⟨n, ?_⟩, ⟨e ≪≫ liftMonIso A⟩⟩
      apply ULift.ext
      change (ℓ ^ n : A) = 0
      simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hn 1
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, Or.inl h⟩)))
  have hi := (inter hcoef).2
  have hpres := (openImmersionLowerShriek_localizing ℓ k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) Λ hΛ cf.i).2.2
  obtain ⟨_, _, hj, _⟩ := hpres
  let A := (localizingClosureProEtale Λ X).ι ⋙
    (openImmersionLowerShriek Λ cf.i).mapDerivedCategory
  let Rp := (lowerStar Λ cf.g).rightDerivedFunctor
  let Du := (openImmersionLowerShriek Λ cr.i).mapDerivedCategory
  let Rr := (lowerStar Λ cr.g).rightDerivedFunctor
  let Ri := (upperStar Λ cg.i).mapDerivedCategory
  let Ru := (upperStar Λ cr.i).mapDerivedCategory
  let Li := (openImmersionLowerShriek Λ cg.i).mapDerivedCategory
  let adjI := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ cg.i
  let adjU := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ cr.i
  let m := fun K ↦ (hi (A.obj K)).choose
  have hm : ∀ K, compositionInterchangeIsNormalized Λ cf.g cg.i bc (A.obj K) (m K) :=
    fun K ↦ (hi (A.obj K)).choose_spec.1
  have hmi : ∀ K, IsIso (m K) :=
    fun K ↦ (hi (A.obj K)).choose_spec.2.2 (hj K)
  let e := fun K ↦ @asIso _ _ _ _ (m K) (hmi K)
  let T := A ⋙ Rp
  let G := (A ⋙ Du) ⋙ Rr
  let T' := ((A ⋙ Du) ⋙ Ru) ⋙ Rp
  let δ : G ⋙ Ri ⟶ T' :=
    Functor.whiskerLeft (A ⋙ Du) (interchangeRestrictionNatTrans Λ cf.g cg.i bc)
  let β : T ≅ T' :=
    Functor.isoWhiskerLeft A (Functor.leftUnitor Rp).symm ≪≫
      Functor.isoWhiskerLeft A (Functor.isoWhiskerRight (asIso adjU.unit) Rp)
  have he : ∀ K, adjI.homEquiv _ _ (e K).hom ≫ δ.app K = β.hom.app K := by
    intro K
    dsimp only [δ, Functor.whiskerLeft_app]
    rw [interchangeRestrictionNatTrans_app]
    simpa only [β, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      compositionInterchangeIsNormalized, e, asIso_hom, adjI, adjU, Rp, Du,
      Functor.comp_obj, Functor.id_obj, T', Ru, bc] using (hm K).trans (Category.id_comp _).symm
  let ei : T ⋙ Li ≅ G := NatIso.ofComponents e
    (fun v ↦ normalizedIso_naturality adjI T T' G δ β e he v)
  let cc : Compactification (f ≫ g) :=
    { Z := cr.Z
      i := cf.i ≫ cr.i
      g := cr.g ≫ cg.g
      comm := by
        calc
          f ≫ g = (cf.i ≫ cf.g) ≫ (cg.i ≫ cg.g) :=
            congrArg₂ (fun a b ↦ a ≫ b) cf.comm cg.comm
          _ = cf.i ≫ (cf.g ≫ cg.i) ≫ cg.g := by simp only [Category.assoc]
          _ = cf.i ≫ (cr.i ≫ cr.g) ≫ cg.g :=
            congrArg (fun a ↦ cf.i ≫ a ≫ cg.g) cr.comm
          _ = (cf.i ≫ cr.i) ≫ (cr.g ≫ cg.g) := by simp only [Category.assoc]
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let bcf : Compactification.BoundaryCompactification f := ⟨⟨cf, inferInstance⟩⟩
  let bcg : Compactification.BoundaryCompactification g := ⟨⟨cg, inferInstance⟩⟩
  let bcc : Compactification.BoundaryCompactification (f ≫ g) :=
    ⟨⟨cc, inferInstanceAs (QuasiCompact (cf.i ≫ cr.i))⟩⟩
  let ep := (refinementDerivedLowerStarComp Λ cr.g cg.g).symm
  let er := (Functor.mapDerivedCategoryNatIso (upperStarComp Λ cf.i cr.i) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar Λ cr.i) (upperStar Λ cf.i)).symm).symm
  let eo := Adjunction.leftAdjointCompIso
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ cf.i)
    adjU (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (cf.i ≫ cr.i)) er
  let ambient :
      ((localizingClosureProEtale Λ X).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ cf) ⋙
          rightDerivedLowerShriekOfCompactification Λ cg ≅
        (localizingClosureProEtale Λ X).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ cc :=
    Functor.isoWhiskerRight ei (lowerStar Λ cg.g).rightDerivedFunctor ≪≫
      Functor.isoWhiskerLeft (A ⋙ Du) ep ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (localizingClosureProEtale Λ X).ι eo)
        (lowerStar Λ (cr.g ≫ cg.g)).rightDerivedFunctor
  refine ⟨bcf, bcg, bcc, ⟨?_⟩⟩
  exact NatIso.ofComponents
    (fun K ↦ (localizingClosureProEtale Λ Z).isoMk (ambient.app K))
    (fun v ↦ (localizingClosureProEtale Λ Z).ι.map_injective (ambient.hom.naturality v))

end AlgebraicGeometry.ProEtale.CondensedRing
