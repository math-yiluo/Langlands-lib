/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.ExceptionalRingTransportFamily

/-! # Invertibility of canonical ring scalar mates -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
  AlgebraicGeometry.Scheme.completedAdicChange AlgebraicGeometry.Scheme.reductionChange
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.presheafToSheaf
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

attribute [local instance] constructionInclusionShift

private def ringFullyFaithful (T : Scheme.{max u v}) (s : RingStage.{max u v} l) :
    (RingStage.inclusion.{u, v} l Ω T s).FullyFaithful :=
  match s with
  | .finite E n => (finiteTorConstructible l E.carrier n n.pos T).fullyFaithfulι
  | .integral E => (finiteTorConstructibleIntegral l E.carrier T).fullyFaithfulι

private theorem liftNaturalIso
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {F G : C₀ ⥤ C₁} {I : C₁ ⥤ C₂} (fully : I.FullyFaithful)
    (z : F ⋙ I ≅ G ⋙ I) :
    ∃ d : F ≅ G, ∀ K, I.map (d.hom.app K) = z.hom.app K := by
  let d : F ≅ G := NatIso.ofComponents
    (fun K ↦ fully.preimageIso (z.app K)) (fun f ↦ by
      apply fully.map_injective
      simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
        Iso.app_hom, fully.map_preimage]
      exact z.hom.naturality f)
  exact ⟨d, fun K ↦ fully.map_preimage (z.hom.app K)⟩

private theorem isAlgClosed_of_equiv
    {K : Type*} {L : Type*} [Field K] [Field L] [IsAlgClosed K] (e : K ≃+* L) :
    IsAlgClosed L := by
  refine ⟨fun p ↦ ?_⟩
  have h := (IsAlgClosed.splits (p.map e.symm.toRingHom)).map e.toRingHom
  have he : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    ext n
    simp
  rwa [he] at h

private theorem mate_whisker
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F F' : A ⥤ C} {G G' : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (t : TwoSquare F L₁ L₂ G)
    (f : F' ⟶ F) (g : G ⟶ G') :
    (mateEquiv a₁ a₂ ((t.whiskerTop f).whiskerBottom g)) =
      Functor.whiskerLeft R₁ f ≫ (mateEquiv a₁ a₂ t) ≫
        Functor.whiskerRight g R₂ := by
  ext N
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [← a₂.unit_naturality_assoc]
  simp only [Functor.comp_map]
  have hg := congrArg R₂.map (g.naturality (a₁.counit.app N))
  simp only [R₂.map_comp] at hg
  rw [← reassoc_of% hg]
  simp

private theorem mate_transfer
    {C₀ C₁ D₀ D₁ : Type*}
    [Category* C₀] [Category* C₁] [Category* D₀] [Category* D₁]
    {F₀ H₀ : C₀ ⥤ D₀} {G₀ J₀ : D₀ ⥤ C₀}
    {F₁ H₁ : C₁ ⥤ D₁} {G₁ J₁ : D₁ ⥤ C₁}
    (a₀ : F₀ ⊣ G₀) (a₁ : F₁ ⊣ G₁) (b₀ : H₀ ⊣ J₀) (b₁ : H₁ ⊣ J₁)
    {SX TX : C₀ ⥤ C₁} {SY TY : D₀ ⥤ D₁}
    (α : F₀ ≅ H₀) (β : F₁ ≅ H₁) (x : SX ≅ TX) (y : SY ≅ TY)
    (q : H₀ ⋙ TY ≅ TX ⋙ H₁)
    (hq : IsIso (mateEquiv b₀ b₁ q.inv)) :
    IsIso (mateEquiv a₀ a₁
      ((((TwoSquare.mk _ _ _ _ q.inv).whiskerTop x.hom).whiskerBottom y.inv).whiskerLeft
        α.inv |>.whiskerRight
        β.hom)) := by
  let m := @asIso _ _ _ _ ((mateEquiv b₀ b₁ q.inv)) hq
  let eα := Functor.isoWhiskerRight ((conjugateIsoEquiv a₀ b₀) α.symm) SX
  let ex := Functor.isoWhiskerLeft J₀ x
  let ey := Functor.isoWhiskerRight y.symm J₁
  let eβ := Functor.isoWhiskerLeft SY ((conjugateIsoEquiv b₁ a₁) β)
  rw [mateEquiv_conjugateEquiv_vcomp a₀ b₁ a₁]
  change IsIso ((mateEquiv a₀ b₁
    ((((TwoSquare.mk _ _ _ _ q.inv).whiskerTop x.hom).whiskerBottom y.inv).whiskerLeft
      α.inv)) ≫ Functor.whiskerLeft SY (conjugateEquiv b₁ a₁ β.hom))
  rw [conjugateEquiv_mateEquiv_vcomp a₀ b₀ b₁]
  change IsIso ((Functor.whiskerRight (conjugateEquiv a₀ b₀ α.inv) SX ≫
    (mateEquiv b₀ b₁
      (((TwoSquare.mk _ _ _ _ q.inv).whiskerTop x.hom).whiskerBottom y.inv))) ≫
      Functor.whiskerLeft SY (conjugateEquiv b₁ a₁ β.hom))
  rw [mate_whisker]
  exact ((eα ≪≫ (ex ≪≫ m ≪≫ ey)) ≪≫ eβ).isIso_hom

private theorem normalized_transfer
    {C₀ C₁ D₀ D₁ E₀ E₁ H₀ H₁ : Type*}
    [Category* C₀] [Category* C₁] [Category* D₀] [Category* D₁]
    [Category* E₀] [Category* E₁] [Category* H₀] [Category* H₁]
    (IX₀ : C₀ ⥤ E₀) (IX₁ : C₁ ⥤ E₁) (IY₀ : D₀ ⥤ H₀) (IY₁ : D₁ ⥤ H₁)
    (P₀ : E₀ ⥤ H₀) (P₁ : E₁ ⥤ H₁) (U : E₀ ⥤ E₁) (V : H₀ ⥤ H₁)
    (γ : P₀ ⋙ V ⟶ U ⋙ P₁)
    {F₀ J₀ : C₀ ⥤ D₀} {F₁ J₁ : C₁ ⥤ D₁}
    {SX TX : C₀ ⥤ C₁} {SY TY : D₀ ⥤ D₁}
    (rF₀ : F₀ ⋙ IY₀ ≅ IX₀ ⋙ P₀) (rJ₀ : J₀ ⋙ IY₀ ≅ IX₀ ⋙ P₀)
    (rF₁ : F₁ ⋙ IY₁ ≅ IX₁ ⋙ P₁) (rJ₁ : J₁ ⋙ IY₁ ≅ IX₁ ⋙ P₁)
    (ρSX : SX ⋙ IX₁ ≅ IX₀ ⋙ U) (ρTX : TX ⋙ IX₁ ≅ IX₀ ⋙ U)
    (ρSY : SY ⋙ IY₁ ≅ IY₀ ⋙ V) (ρTY : TY ⋙ IY₁ ≅ IY₀ ⋙ V)
    (α : F₀ ≅ J₀) (β : F₁ ≅ J₁) (x : SX ≅ TX) (y : SY ≅ TY)
    (hα : ∀ K, IY₀.map (α.hom.app K) ≫ rJ₀.hom.app K = rF₀.hom.app K)
    (hβ : ∀ K, IY₁.map (β.hom.app K) ≫ rJ₁.hom.app K = rF₁.hom.app K)
    (hx : ∀ K, IX₁.map (x.hom.app K) ≫ ρTX.hom.app K = ρSX.hom.app K)
    (hy : ∀ K, IY₁.map (y.hom.app K) ≫ ρTY.hom.app K = ρSY.hom.app K)
    (q : J₀ ⋙ TY ≅ TX ⋙ J₁)
    (hq : ∀ K, IY₁.map (q.hom.app K) ≫ rJ₁.hom.app (TX.obj K) ≫
      P₁.map (ρTX.hom.app K) =
      ρTY.hom.app (J₀.obj K) ≫ V.map (rJ₀.hom.app K) ≫ γ.app (IX₀.obj K)) :
    ∀ K, IY₁.map
      ((Functor.isoWhiskerRight α SY ≪≫ Functor.isoWhiskerLeft J₀ y ≪≫ q ≪≫
        Functor.isoWhiskerRight x.symm J₁ ≪≫ Functor.isoWhiskerLeft SX β.symm).hom.app K) ≫
        rF₁.hom.app (SX.obj K) ≫ P₁.map (ρSX.hom.app K) =
      ρSY.hom.app (F₀.obj K) ≫ V.map (rF₀.hom.app K) ≫ γ.app (IX₀.obj K) := by
  intro K
  have hβ' (N : C₁) :
      IY₁.map (β.inv.app N) ≫ rF₁.hom.app N = rJ₁.hom.app N := by
    rw [← hβ N, ← Category.assoc, ← IY₁.map_comp, Iso.inv_hom_id_app,
      IY₁.map_id, Category.id_comp]
  have hx' : IX₁.map (x.inv.app K) ≫ ρSX.hom.app K = ρTX.hom.app K := by
    rw [← hx K, ← Category.assoc, ← IX₁.map_comp, Iso.inv_hom_id_app,
      IX₁.map_id, Category.id_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hβ' (SX.obj K))]
  rw [reassoc_of% (rJ₁.hom.naturality (x.inv.app K))]
  rw [← P₁.map_comp, hx', hq]
  rw [reassoc_of% (hy (J₀.obj K))]
  rw [reassoc_of% (ρSY.hom.naturality (α.hom.app K))]
  rw [← V.map_comp_assoc, hα]

private theorem ring_invertibility_from_comparison
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    (c : Compactification f) {s t : RingStage.{max u v} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (A : Operation.{u, v} l Ω X Y (s.stage l))
    (B : Operation.{u, v} l Ω X Y (t.stage l))
    {F₀ : C.{u, v} l Ω X (s.stage l) ⥤ C.{u, v} l Ω Y (s.stage l)}
    {G₀ : C.{u, v} l Ω Y (s.stage l) ⥤ C.{u, v} l Ω X (s.stage l)}
    {F₁ : C.{u, v} l Ω X (t.stage l) ⥤ C.{u, v} l Ω Y (t.stage l)}
    {G₁ : C.{u, v} l Ω Y (t.stage l) ⥤ C.{u, v} l Ω X (t.stage l)}
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁)
    (rA : LeftRealization.{u, v} l Ω c s A)
    (r₀ : F₀ ⋙ RingStage.inclusion.{u, v} l Ω Y s ≅
      RingStage.inclusion.{u, v} l Ω X s ⋙ PurCompactSupport.image (s.coefficients l) c)
    (rB : LeftRealization.{u, v} l Ω c t B)
    (r₁ : F₁ ⋙ RingStage.inclusion.{u, v} l Ω Y t ≅
      RingStage.inclusion.{u, v} l Ω X t ⋙ PurCompactSupport.image (t.coefficients l) c)
    (SX : Scalar.{u, v} l Ω a X)
    (TX : C.{u, v} l Ω X (s.stage l) ⥤ C.{u, v} l Ω X (t.stage l))
    (SY : Scalar.{u, v} l Ω a Y)
    (TY : C.{u, v} l Ω Y (s.stage l) ⥤ C.{u, v} l Ω Y (t.stage l))
    (ρTX : TX ⋙ RingStage.inclusion.{u, v} l Ω X t ≅
      RingStage.inclusion.{u, v} l Ω X s ⋙ pbcDerivedExtend (a.map X))
    (ρTY : TY ⋙ RingStage.inclusion.{u, v} l Ω Y t ≅
      RingStage.inclusion.{u, v} l Ω Y s ⋙ pbcDerivedExtend (a.map Y))
    (q₀ : F₀ ⋙ TY ≅ TX ⋙ F₁)
    (hn : ∀ K, (RingStage.inclusion.{u, v} l Ω Y t).map (q₀.hom.app K) ≫
      r₁.hom.app (TX.obj K) ≫
      (PurCompactSupport.image (t.coefficients l) c).map (ρTX.hom.app K) =
      ρTY.hom.app (F₀.obj K) ≫
      (pbcDerivedExtend (a.map Y)).map (r₀.hom.app K) ≫
      (PurCompactSupport.comparison a c).app
        ((RingStage.inclusion.{u, v} l Ω X s).obj K))
    (hm : IsIso (mateEquiv adj₀ adj₁ q₀.inv)) :
    IsIso (Functor.whiskerLeft (RingStage.inclusion.{u, v} l Ω X s)
      (PurCompactSupport.comparison a c)) ∧
    ∀ (q : A.F ⋙ SY.functor ≅ SX.functor ⋙ B.F),
      (∀ K : C.{u, v} l Ω X (s.stage l),
        (RingStage.inclusion.{u, v} l Ω Y t).map (q.hom.app K) ≫
          rB.hom.app (SX.functor.obj K) ≫
          (PurCompactSupport.image (t.coefficients l) c).map (SX.realization.hom.app K) =
        SY.realization.hom.app (A.F.obj K) ≫
          (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
          (PurCompactSupport.comparison a c).app
            ((RingStage.inclusion.{u, v} l Ω X s).obj K)) →
      IsIso (mateEquiv A.adjunction B.adjunction q.inv) := by
  classical
  let IX₀ := RingStage.inclusion.{u, v} l Ω X s
  let IX₁ := RingStage.inclusion.{u, v} l Ω X t
  let IY₀ := RingStage.inclusion.{u, v} l Ω Y s
  let IY₁ := RingStage.inclusion.{u, v} l Ω Y t
  obtain ⟨α, hα⟩ := liftNaturalIso (ringFullyFaithful.{u, v} l Ω Y s) (rA ≪≫ r₀.symm)
  obtain ⟨β, hβ⟩ := liftNaturalIso (ringFullyFaithful.{u, v} l Ω Y t) (rB ≪≫ r₁.symm)
  obtain ⟨x, hx⟩ := liftNaturalIso (ringFullyFaithful.{u, v} l Ω X t)
    (SX.realization ≪≫ ρTX.symm)
  obtain ⟨y, hy⟩ := liftNaturalIso (ringFullyFaithful.{u, v} l Ω Y t)
    (SY.realization ≪≫ ρTY.symm)
  have hα' K : IY₀.map (α.hom.app K) ≫ r₀.hom.app K = rA.hom.app K := by
    rw [hα K]
    simp
  have hβ' K : IY₁.map (β.hom.app K) ≫ r₁.hom.app K = rB.hom.app K := by
    rw [hβ K]
    simp
  have hx' K : IX₁.map (x.hom.app K) ≫ ρTX.hom.app K =
      SX.realization.hom.app K := by
    rw [hx K]
    simp
  have hy' K : IY₁.map (y.hom.app K) ≫ ρTY.hom.app K =
      SY.realization.hom.app K := by
    rw [hy K]
    simp
  let q₁ : A.F ⋙ SY.functor ≅ SX.functor ⋙ B.F :=
    Functor.isoWhiskerRight α SY.functor ≪≫ Functor.isoWhiskerLeft F₀ y ≪≫ q₀ ≪≫
      Functor.isoWhiskerRight x.symm F₁ ≪≫ Functor.isoWhiskerLeft SX.functor β.symm
  have hn₁ := normalized_transfer IX₀ IX₁ IY₀ IY₁
    (PurCompactSupport.image (s.coefficients l) c) (PurCompactSupport.image (t.coefficients l) c)
    (pbcDerivedExtend (a.map X)) (pbcDerivedExtend (a.map Y))
    (PurCompactSupport.comparison a c) rA r₀ rB r₁ SX.realization ρTX
    SY.realization ρTY α β x y hα' hβ' hx' hy' q₀ hn
  refine ⟨?_, ?_⟩
  · have hcomp (K : C.{u, v} l Ω X (s.stage l)) :
        IsIso ((PurCompactSupport.comparison a c).app (IX₀.obj K)) := by
      let e := ρTY.app (F₀.obj K) ≪≫
        (pbcDerivedExtend (a.map Y)).mapIso (r₀.app K)
      let z := IY₁.mapIso (q₀.app K) ≪≫ r₁.app (TX.obj K) ≪≫
        (PurCompactSupport.image (t.coefficients l) c).mapIso (ρTX.app K)
      have he : e.hom ≫ (PurCompactSupport.comparison a c).app (IX₀.obj K) = z.hom := by
        simpa only [e, z, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
          using (hn K).symm
      have : IsIso e.hom := e.isIso_hom
      have : IsIso (e.hom ≫ (PurCompactSupport.comparison a c).app (IX₀.obj K)) := by
        rw [he]
        exact z.isIso_hom
      exact IsIso.of_isIso_comp_left e.hom _
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hcomp
  · intro q hq
    have he : q = q₁ := by
      apply Iso.ext
      ext K
      apply (ringFullyFaithful.{u, v} l Ω Y t).map_injective
      let e := rB.app (SX.functor.obj K) ≪≫
        (PurCompactSupport.image (t.coefficients l) c).mapIso (SX.realization.app K)
      have : IsIso e.hom := e.isIso_hom
      apply (cancel_mono e.hom).mp
      exact (hq K).trans (hn₁ K).symm
    rw [he]
    have hi : q₁.inv =
        ((((TwoSquare.mk _ _ _ _ q₀.inv).whiskerTop x.hom).whiskerBottom y.inv).whiskerLeft
          α.inv |>.whiskerRight
          β.hom) := by
      ext K
      simp [q₁, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
        TwoSquare.whiskerLeft, TwoSquare.whiskerRight, Category.assoc]
    rw [hi]
    exact mate_transfer A.adjunction B.adjunction adj₀ adj₁ α β x y q₀ hm

/-- The geometric invertibility tests for the canonical scalar comparison and its mate.
Source: Zheng, Lemma 5.22, Construction 5.25, Propositions 5.24 and 5.26;
scalar-mates plan steps 2, 3 and 6
(blueprint: lem-sf-ring-canonical-scalar-invertibility).

Proof: for finite generators take the finite transported scalar mates. The ambient
proper/open scalar map is their left realization. Compare any supplied adjunctions
with these by full inclusion on the left and right-adjoint uniqueness on the right;
the counit equation identifies the right comparison with mateEquiv of inverse q.
For integral reduction reconstruct the normalized system adjunction from the
reduction/total-limit equivalence and the actual proper/open system realization.
Construct the system proper scalar projection and open tensor maps before taking
limit, and transpose their composite using the system counit. Their evaluations
are the finite mates by the actual unit and counit comparisons. Their cones have
zero evaluations, hence they are invertible in the derived system category.
For completed extension apply the finite-free system comparison and cofinal
recovery of the ramified subsequence. Reconstruction transports these maps and
their counit-transpose formula to the integral categories. The simultaneous
proper/open realization identifies the resulting left map with precisely the
ambient comparison in the first conclusion. Transfer to arbitrary supplied
realizations by the unique full-inclusion comparison. Any q satisfying the stated
normalization is that transferred map, since the target inclusion is faithful;
its mate is therefore the transferred invertible system mate. For identities
use tensor multiplication; for composites use tensor associativity and mate
pasting, inducting on Allowed. The normalized maps are maps of systems before
evaluation; no faithfulness of derived evaluation on morphisms is assumed.
The zero case uses zero objects; the positive-index convention includes the
residue level and never introduces level zero. This statement asserts only
invertibility and constructs no scalar functor, shift structure or counit datum. -/
theorem ring_canonical_scalar_invertibility
    (D : FiniteFieldDatum.{max u v}) (_hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {s t : RingStage.{max u v} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (_ha : Allowed l a)
    (A : Operation.{u, v} l Ω X Y (s.stage l))
    (B : Operation.{u, v} l Ω X Y (t.stage l))
    (rA : LeftRealization.{u, v} l Ω c s A)
    (rB : LeftRealization.{u, v} l Ω c t B)
    (SX : Scalar.{u, v} l Ω a X) (SY : Scalar.{u, v} l Ω a Y) :
    IsIso (Functor.whiskerLeft (RingStage.inclusion.{u, v} l Ω X s)
      (PurCompactSupport.comparison a c)) ∧
    ∀ (q : A.F ⋙ SY.functor ≅ SX.functor ⋙ B.F),
      (∀ K : C.{u, v} l Ω X (s.stage l),
        (RingStage.inclusion.{u, v} l Ω Y t).map (q.hom.app K) ≫
          rB.hom.app (SX.functor.obj K) ≫
          (PurCompactSupport.image (t.coefficients l) c).map (SX.realization.hom.app K) =
        SY.realization.hom.app (A.F.obj K) ≫
          (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
          (PurCompactSupport.comparison a c).app
            ((RingStage.inclusion.{u, v} l Ω X s).obj K)) →
      IsIso (mateEquiv A.adjunction B.adjunction q.inv) := by
  classical
  let Ω' := ULift.{u} Ω
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (Padic l)
  have : IsAlgClosure (Padic l) Ω' :=
    { isAlgClosed := isAlgClosed_of_equiv (ULift.ringEquiv.symm : Ω ≃+* Ω')
      isAlgebraic := Algebra.IsAlgebraic.of_injective
        (ULift.algEquiv (R := Padic l)).toAlgHom ULift.down_injective }
  obtain ⟨operation, left, ⟨tr⟩⟩ :=
    exists_exceptional_ring_transport_family l Ω' D _hl f c
  obtain ⟨d, red, sys⟩ := ExceptionalIntegralScalar.exceptionalIntegralScalarMates_core
    l Ω' D _hl c operation left tr
  let := (d.scalar a _ha true).commShift
  let := (d.scalar a _ha false).commShift
  let A₀ := operation s
  let B₀ := operation t
  let r₀ := left s
  let r₁ := left t
  let dc := d.comparison a _ha
  have hn := d.comparison_normalized a _ha
  let sq : TwoSquare (d.scalar a _ha true).functor A₀.F B₀.F
      (d.scalar a _ha false).functor := TwoSquare.mk _ _ _ _ dc.q.inv
  have hm : IsIso (mateEquiv A₀.adjunction B₀.adjunction sq) := by
    have he : (mateEquiv A₀.adjunction B₀.adjunction sq) = dc.b.hom := by
      apply NatTrans.ext
      funext N
      apply (B₀.adjunction.homEquiv _ _).symm.injective
      simp only [Adjunction.homEquiv_symm_apply]
      rw [mateEquiv_counit A₀.adjunction B₀.adjunction sq N]
      dsimp only [sq, TwoSquare.mk]
      rw [← dc.counit N]
      dsimp only [A₀, B₀]
      simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rw [he]
    infer_instance
  cases s <;> cases t
  all_goals
    exact ring_invertibility_from_comparison.{u, v} l Ω c a A B A₀.adjunction B₀.adjunction
      rA r₀ rB r₁ SX (d.scalar a _ha true).functor SY (d.scalar a _ha false).functor
      (d.scalar a _ha true).realization (d.scalar a _ha false).realization dc.q hn hm

end WeilConjectures.ConstructibleExceptionalCoefficients
