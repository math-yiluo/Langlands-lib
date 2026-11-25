/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarData
import WeilConjectures.SixFunctors.PurCompactSupport.FiniteScalarPresentationCompatibility
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRegularQuotientReverseAdjunction
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree

/-! # Invertibility of the prescribed exceptional right scalar mate

Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: lem-sf-exceptional-integral-right-scalar-invertibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u a b av bv x y xv yv
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private def ringFullyFaithful (T : Scheme.{u}) (s : RingStage.{u} l) :
    (RingStage.inclusion.{u} l Ω T s).FullyFaithful :=
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
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (A : Operation.{u} l Ω X Y (s.stage l))
    (B : Operation.{u} l Ω X Y (t.stage l))
    {F₀ : C.{u} l Ω X (s.stage l) ⥤ C.{u} l Ω Y (s.stage l)}
    {G₀ : C.{u} l Ω Y (s.stage l) ⥤ C.{u} l Ω X (s.stage l)}
    {F₁ : C.{u} l Ω X (t.stage l) ⥤ C.{u} l Ω Y (t.stage l)}
    {G₁ : C.{u} l Ω Y (t.stage l) ⥤ C.{u} l Ω X (t.stage l)}
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁)
    (rA : LeftRealization.{u} l Ω c s A)
    (r₀ : F₀ ⋙ RingStage.inclusion.{u} l Ω Y s ≅
      RingStage.inclusion.{u} l Ω X s ⋙ PurCompactSupport.image (s.coefficients l) c)
    (rB : LeftRealization.{u} l Ω c t B)
    (r₁ : F₁ ⋙ RingStage.inclusion.{u} l Ω Y t ≅
      RingStage.inclusion.{u} l Ω X t ⋙ PurCompactSupport.image (t.coefficients l) c)
    (SX : Scalar.{u} l Ω a X)
    (TX : C.{u} l Ω X (s.stage l) ⥤ C.{u} l Ω X (t.stage l))
    (SY : Scalar.{u} l Ω a Y)
    (TY : C.{u} l Ω Y (s.stage l) ⥤ C.{u} l Ω Y (t.stage l))
    (ρTX : TX ⋙ RingStage.inclusion.{u} l Ω X t ≅
      RingStage.inclusion.{u} l Ω X s ⋙ pbcDerivedExtend (a.map X))
    (ρTY : TY ⋙ RingStage.inclusion.{u} l Ω Y t ≅
      RingStage.inclusion.{u} l Ω Y s ⋙ pbcDerivedExtend (a.map Y))
    (q₀ : F₀ ⋙ TY ≅ TX ⋙ F₁)
    (hn : ∀ K, (RingStage.inclusion.{u} l Ω Y t).map (q₀.hom.app K) ≫
      r₁.hom.app (TX.obj K) ≫
      (PurCompactSupport.image (t.coefficients l) c).map (ρTX.hom.app K) =
      ρTY.hom.app (F₀.obj K) ≫
      (pbcDerivedExtend (a.map Y)).map (r₀.hom.app K) ≫
      (PurCompactSupport.comparison a c).app
        ((RingStage.inclusion.{u} l Ω X s).obj K))
    (hm : IsIso (mateEquiv adj₀ adj₁ q₀.inv)) :
    IsIso (Functor.whiskerLeft (RingStage.inclusion.{u} l Ω X s)
      (PurCompactSupport.comparison a c)) ∧
    ∀ (q : A.F ⋙ SY.functor ≅ SX.functor ⋙ B.F),
      (∀ K : C.{u} l Ω X (s.stage l),
        (RingStage.inclusion.{u} l Ω Y t).map (q.hom.app K) ≫
          rB.hom.app (SX.functor.obj K) ≫
          (PurCompactSupport.image (t.coefficients l) c).map (SX.realization.hom.app K) =
        SY.realization.hom.app (A.F.obj K) ≫
          (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
          (PurCompactSupport.comparison a c).app
            ((RingStage.inclusion.{u} l Ω X s).obj K)) →
      IsIso (mateEquiv A.adjunction B.adjunction q.inv) := by
  classical
  let IX₀ := RingStage.inclusion.{u} l Ω X s
  let IX₁ := RingStage.inclusion.{u} l Ω X t
  let IY₀ := RingStage.inclusion.{u} l Ω Y s
  let IY₁ := RingStage.inclusion.{u} l Ω Y t
  obtain ⟨α, hα⟩ := liftNaturalIso (ringFullyFaithful.{u} l Ω Y s) (rA ≪≫ r₀.symm)
  obtain ⟨β, hβ⟩ := liftNaturalIso (ringFullyFaithful.{u} l Ω Y t) (rB ≪≫ r₁.symm)
  obtain ⟨x, hx⟩ := liftNaturalIso (ringFullyFaithful.{u} l Ω X t)
    (SX.realization ≪≫ ρTX.symm)
  obtain ⟨y, hy⟩ := liftNaturalIso (ringFullyFaithful.{u} l Ω Y t)
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
  · have hcomp (K : C.{u} l Ω X (s.stage l)) :
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
      apply (ringFullyFaithful.{u} l Ω Y t).map_injective
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

private theorem rightMate_of_reverseAdjunction
    {A : Type a} {B : Type b} {C : Type x} {D : Type y}
    [Category.{av} A] [Category.{bv} B] [Category.{xv} C] [Category.{yv} D]
    {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
    {EX : A ⥤ C} {EY : B ⥤ D} {RX : C ⥤ A} {RY : D ⥤ B}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (ax : RX ⊣ EX) (ay : RY ⊣ EY)
    (q : F ⋙ EY ≅ EX ⋙ F')
    (h : IsIso ((mateEquiv ax ay).symm q.inv)) :
    IsIso (mateEquiv adj adj' q.inv) := by
  let α := ((mateEquiv ax ay).symm q.inv)
  let : IsIso α := h
  have he := iterated_mateEquiv_conjugateEquiv ax ay adj' adj
    ((mateEquiv ax ay).symm q.inv)
  rw [Equiv.apply_symm_apply] at he
  rw [he]
  change IsIso ((conjugateIsoEquiv (ax.comp adj) (adj'.comp ay)) (asIso α)).hom
  infer_instance

section Identity
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) {TX : A ⥤ A} {TY : B ⥤ B}
    (q : F ⋙ TY ≅ TX ⋙ F) (beta : G ⋙ TX ⟶ TY ⋙ G)
    (hc : ∀ L, q.hom.app (G.obj L) ≫ F.map (beta.app L) ≫
      adj.counit.app (TY.obj L) = TY.map (adj.counit.app L))
    (uX : TX ≅ 𝟭 A) (uY : TY ≅ 𝟭 B)
    (hleft : ∀ K, q.hom.app K ≫ F.map (uX.hom.app K) = uY.hom.app (F.obj K))
include hc hleft in
private theorem rightIdentity (L : B) :
    beta.app L ≫ G.map (uY.hom.app L) = uX.hom.app (G.obj L) := by
  apply (adj.homEquiv _ _).symm.injective
  change F.map _ ≫ adj.counit.app _ = F.map _ ≫ adj.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [adj.counit_naturality]
  apply (cancel_epi (q.hom.app (G.obj L))).1
  calc
    _ = TY.map (adj.counit.app L) ≫ uY.hom.app L := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ uY.hom.app L) (hc L)
    _ = uY.hom.app (F.obj (G.obj L)) ≫ adj.counit.app L := uY.hom.naturality _
    _ = _ := by rw [← hleft, Category.assoc]; rfl
end Identity

section
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (z : LeftMates l Ω c operation left)

private theorem mateCounit {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a) (N : C.{u} l Ω Y (s.stage l)) :
    (z.q a ha).hom.app ((operation s).G.obj N) ≫
        (operation t).F.map ((z.mate l Ω a ha).app N) ≫
        (operation t).adjunction.counit.app ((z.scalar a ha false).functor.obj N) =
      (z.scalar a ha false).functor.map ((operation s).adjunction.counit.app N) := by
  rw [show (operation t).F.map ((z.mate l Ω a ha).app N) ≫
      (operation t).adjunction.counit.app ((z.scalar a ha false).functor.obj N) =
      (z.q a ha).inv.app ((operation s).G.obj N) ≫
        (z.scalar a ha false).functor.map ((operation s).adjunction.counit.app N) from
    mateEquiv_counit (operation s).adjunction (operation t).adjunction (z.q a ha).inv N]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private theorem mateComposite {s t r : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
    (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
    (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
    (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d)
    (N : C.{u} l Ω Y (s.stage l)) :
    (z.scalar b hb true).functor.map ((z.mate l Ω a ha).app N) ≫
        (z.mate l Ω b hb).app ((z.scalar a ha false).functor.obj N) ≫
        (operation r).G.map
          ((z.scalarComposition a b d h ha hb hd false).iso.hom.app N) =
      (z.scalarComposition a b d h ha hb hd true).iso.hom.app ((operation s).G.obj N) ≫
        (z.mate l Ω d hd).app N := by
  let A := operation s
  let B := operation t
  let D := operation r
  let TX := (z.scalar a ha true).functor
  let TY := (z.scalar a ha false).functor
  let UX := (z.scalar b hb true).functor
  let UY := (z.scalar b hb false).functor
  let VX := (z.scalar d hd true).functor
  let VY := (z.scalar d hd false).functor
  let q₁ := z.q a ha
  let q₂ := z.q b hb
  let q₃ := z.q d hd
  let b₁ := z.mate l Ω a ha
  let b₂ := z.mate l Ω b hb
  let b₃ := z.mate l Ω d hd
  let αX := (z.scalarComposition a b d h ha hb hd true).iso
  let αY := (z.scalarComposition a b d h ha hb hd false).iso
  have hleft := z.leftCocycle a b d h ha hb hd
  have hc₁ := mateCounit l Ω z a ha
  have hc₂ := mateCounit l Ω z b hb
  have hc₃ := mateCounit l Ω z d hd
  change UX.map (b₁.app N) ≫ b₂.app (TY.obj N) ≫ D.G.map (αY.hom.app N) =
    αX.hom.app (A.G.obj N) ≫ b₃.app N
  apply (D.adjunction.homEquiv _ _).symm.injective
  change D.F.map _ ≫ D.adjunction.counit.app _ =
    D.F.map _ ≫ D.adjunction.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [D.adjunction.counit_naturality]
  apply (cancel_epi (UY.map (q₁.hom.app (A.G.obj N)) ≫
    q₂.hom.app (TX.obj (A.G.obj N)))).1
  simp only [Category.assoc]
  have hn := q₂.hom.naturality (b₁.app N)
  dsimp only [Functor.comp_map] at hn
  have hα := αY.hom.naturality (A.adjunction.counit.app N)
  dsimp only [Functor.comp_map] at hα
  calc
    _ = UY.map (q₁.hom.app (A.G.obj N)) ≫
        UY.map (B.F.map (b₁.app N)) ≫ q₂.hom.app (B.G.obj (TY.obj N)) ≫
        D.F.map (b₂.app (TY.obj N)) ≫
        D.adjunction.counit.app (UY.obj (TY.obj N)) ≫ αY.hom.app N := by
      rw [reassoc_of% hn]
    _ = UY.map (q₁.hom.app (A.G.obj N)) ≫ UY.map (B.F.map (b₁.app N)) ≫
        UY.map (B.adjunction.counit.app (TY.obj N)) ≫ αY.hom.app N := by
      rw [reassoc_of% (hc₂ (TY.obj N))]
    _ = UY.map (TY.map (A.adjunction.counit.app N)) ≫ αY.hom.app N := by
      rw [← UY.map_comp_assoc, ← UY.map_comp_assoc, Category.assoc, hc₁]
    _ = αY.hom.app (A.F.obj (A.G.obj N)) ≫ VY.map (A.adjunction.counit.app N) := hα
    _ = αY.hom.app (A.F.obj (A.G.obj N)) ≫ q₃.hom.app (A.G.obj N) ≫
        D.F.map (b₃.app N) ≫ D.adjunction.counit.app (VY.obj N) := by rw [hc₃ N]
    _ = _ := by rw [← reassoc_of% (hleft (A.G.obj N))]

end

private def leftReductionEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (d : LeftMates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ) (side : Bool)
    (R : Reconstruction l E (endpoint X Y side)) :
    (d.scalar (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) side).functor ≅
      R.equivalence.functor ⋙ R.evaluation n :=
  Functor.fullyFaithfulCancelRight
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n)
      (endpoint X Y side)).ι
    (eqToIso (d.finiteScalar_eq (s := .integral E) E ⟨n + 1, Nat.succ_pos n⟩
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) side) ≪≫
      isoWhiskerLeft (finiteTorConstructibleIntegral l E.carrier (endpoint X Y side)).ι
        (PurCompactSupport.finiteReductionIso l E.carrier (endpoint X Y side) n) ≪≫
      (R.evaluationRealization l E (endpoint X Y side) n).symm)

private theorem finiteRightMate
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (z : LeftMates l Ω c operation left)
    (E L : FieldStage.{u} l) (n m : ℕ+)
    (a : PurCompactSupport.Change
      ((RingStage.finite E n).coefficients l)
      ((RingStage.finite L m).coefficients l))
    (ha : Allowed l a)
    (φ : Padic.coefficientExtensionRing l E.carrier n →+*
      Padic.coefficientExtensionRing l L.carrier m)
    (hφ : ∀ T : Scheme.{u}, a.map T = proEtaleConstantRingMap (T := T) φ) :
    IsIso (z.mate l Ω a ha) := by
  classical
  rcases n with ⟨_ | n, hn⟩
  · omega
  rcases m with ⟨_ | m, hm⟩
  · omega
  cases a with
  | mk amap asquare =>
    have hm : amap = fun T ↦ proEtaleConstantRingMap (T := T) φ := funext hφ
    subst amap
    let a : PurCompactSupport.Change
        ((RingStage.finite E ⟨n + 1, Nat.succ_pos n⟩).coefficients l)
        ((RingStage.finite L ⟨m + 1, Nat.succ_pos m⟩).coefficients l) :=
      ⟨fun T ↦ proEtaleConstantRingMap (T := T) φ, asquare⟩
    obtain ⟨d⟩ := ExceptionalFiniteScalar.exceptionalFiniteScalarMates D l hl
      E.carrier L.carrier n m φ f c
    let r₀ := d.source.left ≪≫ isoWhiskerLeft
      (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) X).ι
      (PurCompactSupport.finiteImageIso l E.carrier n c).symm
    let r₁ := d.target.left ≪≫ isoWhiskerLeft
      (finiteTorConstructible l L.carrier (m + 1) (Nat.succ_pos m) X).ι
      (PurCompactSupport.finiteImageIso l L.carrier m c).symm
    have hc := eq_of_heq (PurCompactSupport.finiteScalarPresentationCompatibility
      l E.carrier L.carrier n m a φ (fun _ ↦ rfl) c)
    have hn (K : finiteTorConstructibleCategory l E.carrier (n + 1)
        (Nat.succ_pos n) X) :
        (finiteTorConstructible l L.carrier (m + 1) (Nat.succ_pos m) Y).ι.map
            (d.q.hom.app K) ≫ r₁.hom.app (d.scalarX.functor.obj K) ≫
            (PurCompactSupport.image
              ((RingStage.finite L ⟨m + 1, Nat.succ_pos m⟩).coefficients l) c).map
              ((eqToIso d.scalarX.scalar_eq).hom.app K) =
          (eqToIso d.scalarY.scalar_eq).hom.app (d.source.F.obj K) ≫
            (pbcDerivedExtend (a.map Y)).map (r₀.hom.app K) ≫
            (PurCompactSupport.comparison a c).app K.obj := by
      rw [hc]
      simp only [r₀, r₁, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
        Functor.map_comp, Category.assoc]
      simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
      dsimp only [a]
      erw [CategoryTheory.Functor.map_id]
      convert congrArg (fun k ↦ k ≫
        (PurCompactSupport.finiteImageIso l L.carrier m c).inv.app
          ((pbcDerivedExtend (proEtaleConstantRingMap (T := X) φ)).obj K.obj))
        (d.q_normalized K) using 1
      · erw [Category.comp_id]
        exact (Category.assoc _ _ _).symm
      · simp only [Category.assoc]
        erw [← (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) φ)).map_comp_assoc
          ((PurCompactSupport.finiteImageIso l E.carrier n c).inv.app K.obj)
          ((PurCompactSupport.finiteImageIso l E.carrier n c).hom.app K.obj),
          Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    have hi : IsIso (mateEquiv d.source.adjunction d.target.adjunction d.q.inv) := by
      have he : (mateEquiv d.source.adjunction d.target.adjunction d.q.inv) =
          d.b.hom := by
        apply NatTrans.ext
        funext N
        apply (d.target.adjunction.homEquiv _ _).symm.injective
        change d.target.F.map _ ≫ d.target.adjunction.counit.app _ =
          d.target.F.map _ ≫ d.target.adjunction.counit.app _
        rw [mateEquiv_counit]
        apply (cancel_epi (d.q.hom.app (d.source.G.obj N))).1
        simpa only [Iso.hom_inv_id_app_assoc] using (d.counit N).symm
      rw [he]
      infer_instance
    exact (ring_invertibility_from_comparison l Ω c
      (a := a) (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩))
      (operation (.finite L ⟨m + 1, Nat.succ_pos m⟩))
      d.source.adjunction d.target.adjunction
      (left (.finite E ⟨n + 1, Nat.succ_pos n⟩)) r₀
      (left (.finite L ⟨m + 1, Nat.succ_pos m⟩)) r₁
      (z.scalar a ha true) d.scalarX.functor (z.scalar a ha false) d.scalarY.functor
      (eqToIso d.scalarX.scalar_eq) (eqToIso d.scalarY.scalar_eq) d.q hn hi).2
        (z.q a ha) (z.q_normalized a ha)

private theorem reductionRightMate
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (_transport : Transported l Ω D hl c operation left)
    (d : LeftMates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ) :
    IsIso (d.mate l Ω (s := .integral E)
      (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)) := by
  obtain ⟨RX, RY, ax, ay, h⟩ := exceptionalRegularQuotientReverseAdjunction
    l Ω D hl c operation left d E n
  exact rightMate_of_reverseAdjunction
    (operation (.integral E)).adjunction
    (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction ax ay
    (d.q _ (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)) h

private def composeChange {R S T : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) (b : PurCompactSupport.Change S T) :
    PurCompactSupport.Change R T where
  map W := a.map W ≫ b.map W
  square {U V} g := by
    simp only [← Category.assoc]
    rw [a.square g]
    simp only [Category.assoc]
    rw [b.square g, ← Functor.map_comp_assoc]

private theorem positiveProjectionQuotient (E : FieldStage.{u} l) (m n : ℕ+)
    (h : (n : ℕ) ≤ m) (T : Scheme.{u}) :
    (PurCompactSupport.reduction l E.carrier m m.pos).map T ≫
      (PurCompactSupport.finiteQuotientChange l E.carrier m n m.pos n.pos h).map T =
        (PurCompactSupport.reduction l E.carrier n n.pos).map T := by
  rcases m with ⟨_ | m, hm⟩
  · omega
  rcases n with ⟨_ | n, hn⟩
  · omega
  change n + 1 ≤ m + 1 at h
  exact compactSupportProjection_comp l E.carrier T m n (by omega)

private theorem reductionDetectsIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (z : LeftMates l Ω c operation left) (E : FieldStage.{u} l) (side : Bool)
    (R : Reconstruction l E (endpoint X Y side))
    {K N : C.{u} l Ω (endpoint X Y side) (.integral E)} (v : K ⟶ N)
    (h : ∀ n : ℕ, IsIso ((z.scalar (s := .integral E)
      (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) side).functor.map v)) : IsIso v := by
  have hR : IsIso (R.equivalence.functor.map v) := by
    have hI : IsIso ((sequenceProperty l E (endpoint X Y side)).ι.map
        (R.equivalence.functor.map v)) := by
      apply (R.calculus.isIso_iff_evaluations _).2
      intro n
      have he := (NatIso.isIso_map_iff
        (leftReductionEvaluation l Ω z E n side R) v).1 (h n)
      have : IsIso ((R.evaluation n).map (R.equivalence.functor.map v)) := he
      have hi : IsIso ((R.evaluation n ⋙
          (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n)
            (endpoint X Y side)).ι).map (R.equivalence.functor.map v)) := by
        change IsIso ((finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n)
          (endpoint X Y side)).ι.map
            ((R.evaluation n).map (R.equivalence.functor.map v)))
        infer_instance
      exact (NatIso.isIso_map_iff (eqToIso (R.evaluation_eq n))
        (R.equivalence.functor.map v)).1 hi
    exact isIso_of_reflects_iso (R.equivalence.functor.map v)
      (sequenceProperty l E (endpoint X Y side)).ι
  exact isIso_of_reflects_iso v R.equivalence.functor

private theorem cofinalReductionDetectsIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (z : LeftMates l Ω c operation left) (E : FieldStage.{u} l) (side : Bool)
    (R : Reconstruction l E (endpoint X Y side)) (e : ℕ+)
    {K N : C.{u} l Ω (endpoint X Y side) (.integral E)} (v : K ⟶ N)
    (h : ∀ n : ℕ+, IsIso ((z.scalar (s := .integral E)
      (t := .finite E ⟨e * n, Nat.mul_pos e.pos n.pos⟩)
      (PurCompactSupport.reduction l E.carrier (e * n) (Nat.mul_pos e.pos n.pos))
      (Allowed.reduction E ⟨e * n, Nat.mul_pos e.pos n.pos⟩) side).functor.map v)) :
    IsIso v := by
  apply reductionDetectsIso l Ω z E side R v
  intro n
  let k : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  let m : ℕ+ := ⟨e * k, Nat.mul_pos e.pos k.pos⟩
  have hkm : (k : ℕ) ≤ m := by
    exact le_mul_of_one_le_left (Nat.zero_le (k : ℕ)) e.pos
  let a : PurCompactSupport.Change ((RingStage.integral E).coefficients l)
      ((RingStage.finite E m).coefficients l) :=
    PurCompactSupport.reduction l E.carrier m m.pos
  let b : PurCompactSupport.Change ((RingStage.finite E m).coefficients l)
      ((RingStage.finite E k).coefficients l) :=
    PurCompactSupport.finiteQuotientChange l E.carrier m k m.pos k.pos hkm
  let d : PurCompactSupport.Change ((RingStage.integral E).coefficients l)
      ((RingStage.finite E k).coefficients l) :=
    PurCompactSupport.reduction l E.carrier k k.pos
  let ha := Allowed.reduction E m
  let hb := Allowed.quotient E m k hkm
  let hd := Allowed.reduction E k
  let α := (z.scalarComposition a b d
    (positiveProjectionQuotient l E m k hkm) ha hb hd side).iso
  have : IsIso ((z.scalar a ha side).functor.map v) := h k
  have hi : IsIso (((z.scalar a ha side).functor ⋙
      (z.scalar b hb side).functor).map v) := by
    change IsIso ((z.scalar b hb side).functor.map
      ((z.scalar a ha side).functor.map v))
    infer_instance
  exact (NatIso.isIso_map_iff α v).1 hi

private theorem positiveReductionRightMate
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left)
    (z : LeftMates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ+) :
    IsIso (z.mate l Ω (s := .integral E) (t := .finite E n)
      (PurCompactSupport.reduction l E.carrier n n.pos)
      (Allowed.reduction E n)) := by
  rcases n with ⟨_ | n, hn⟩
  · omega
  exact reductionRightMate l Ω D hl c operation left transport z E n

private theorem existsRamification (E L : FieldStage.{u} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) :
    ∃ e : ℕ+, PurCompactSupport.Ramification l E.carrier L.carrier i e := by
  obtain ⟨w, e, he, hw⟩ := integral_ramification l E.carrier L.carrier i
  refine ⟨⟨e, he⟩, ?_⟩
  change Ideal.map _ (Ideal.span {_} ^ 1) = Ideal.span {_} ^ e
  rw [pow_one, Ideal.map_span, Set.image_singleton, hw,
    Ideal.span_singleton_mul_left_unit w.isUnit, Ideal.span_singleton_pow]

private theorem completedRightMate
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left)
    (z : LeftMates l Ω c operation left) (E L : FieldStage.{u} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) :
    IsIso (z.mate l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i)
      (Allowed.integral E L i)) := by
  obtain ⟨e, he⟩ := existsRamification l E L i
  let a : PurCompactSupport.Change ((RingStage.integral E).coefficients l)
      ((RingStage.integral L).coefficients l) :=
    PurCompactSupport.completedChange l E.carrier L.carrier i
  let ha := Allowed.integral E L i
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  apply cofinalReductionDetectsIso l Ω z L true (transport.reconstruction L true) e
  intro n
  let m : ℕ+ := ⟨e * n, Nat.mul_pos e.pos n.pos⟩
  let b : PurCompactSupport.Change ((RingStage.integral L).coefficients l)
      ((RingStage.finite L m).coefficients l) :=
    PurCompactSupport.reduction l L.carrier m m.pos
  let hb := Allowed.reduction L m
  let r : PurCompactSupport.Change ((RingStage.integral E).coefficients l)
      ((RingStage.finite E n).coefficients l) :=
    PurCompactSupport.reduction l E.carrier n n.pos
  let hr := Allowed.reduction E n
  let s : PurCompactSupport.Change ((RingStage.finite E n).coefficients l)
      ((RingStage.finite L m).coefficients l) :=
    PurCompactSupport.finiteChange l E.carrier L.carrier i e he e.pos n n.pos
  let hs := Allowed.ramified E L i e he n
  let d : PurCompactSupport.Change ((RingStage.integral E).coefficients l)
      ((RingStage.finite L m).coefficients l) := composeChange r s
  let hd := Allowed.comp r s d (fun _ ↦ rfl) hr hs
  have : IsIso (z.mate l Ω r hr) :=
    positiveReductionRightMate l Ω D hl c operation left transport z E n
  have : IsIso (z.mate l Ω s hs) := finiteRightMate l Ω D hl c operation left z
    E L n m s hs (PurCompactSupport.ramifiedMap l E.carrier L.carrier i e he n)
    (fun _ ↦ rfl)
  have : IsIso (z.mate l Ω d hd) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    have hcomp := mateComposite l Ω z r s d (fun _ ↦ rfl) hr hs hd M
    have : IsIso ((z.scalarComposition r s d (fun _ ↦ rfl) hr hs hd true).iso.hom.app
        ((operation (.integral E)).G.obj M) ≫ (z.mate l Ω d hd).app M) := by
      rw [← hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((z.scalarComposition r s d (fun _ ↦ rfl) hr hs hd true).iso.hom.app
        ((operation (.integral E)).G.obj M)) _
  have : IsIso (z.mate l Ω b hb) :=
    positiveReductionRightMate l Ω D hl c operation left transport z L m
  have hsq : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T :=
    PurCompactSupport.ramified_reduction_square l E.carrier L.carrier i e he e.pos n n.pos
  have hcomp := mateComposite l Ω z a b d hsq ha hb hd N
  have : IsIso ((z.scalar b hb true).functor.map ((z.mate l Ω a ha).app N) ≫
      ((z.mate l Ω b hb).app ((z.scalar a ha false).functor.obj N) ≫
        (operation (.finite L m)).G.map
          ((z.scalarComposition a b d hsq ha hb hd false).iso.hom.app N))) := by
    rw [hcomp]
    infer_instance
  change IsIso ((z.scalar b hb true).functor.map ((z.mate l Ω a ha).app N))
  exact IsIso.of_isIso_comp_right _
    ((z.mate l Ω b hb).app ((z.scalar a ha false).functor.obj N) ≫
      (operation (.finite L m)).G.map
        ((z.scalarComposition a b d hsq ha hb hd false).iso.hom.app N))

/-- The counit transpose of the normalized left comparison is invertible.
Source: Zheng, Lemma 5.22 and Proposition 5.26; finite-free scalar mates on
ordinary etale systems and their cofinal ramified recovery.
Proof: for finite coefficient generators use the ordinary etale constant-coefficient
exceptional tensor theorem, then transport along constructible-origin comparison.
For integral reduction, evaluate the actual system adjunction and reconstruct its
counit transpose. For completed inclusion, the selected-level finite-free right
mates are invertible; cofinal recovery and reconstruction carry them to the
prescribed right mate because its counit transpose is the normalized left map.
For identities use the scalar multiplication unitor. For composites use naturality
and the two counit equations to identify the composite right comparison with the
mate of the left composite; balanced scalar associators identify it with the
prescribed mate. Invertibility is preserved by each transport and composition.
(blueprint: lem-sf-exceptional-integral-right-scalar-invertibility). -/
theorem exceptionalIntegralRightScalarInvertibility
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left)
    (z : LeftMates l Ω c operation left) {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a) : IsIso (z.mate l Ω a ha) := by
  induction ha with
  | quotient E m n h =>
    obtain ⟨m, hm⟩ := m
    obtain ⟨n, hn⟩ := n
    cases m with
    | zero => omega
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        apply finiteRightMate l Ω D hl c operation left z E E ⟨m + 1, hm⟩ ⟨n + 1, hn⟩ _ _
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right h))
        intro T
        rfl
  | ramified E L i e he n =>
    exact finiteRightMate l Ω D hl c operation left z E L n
      ⟨e * n, Nat.mul_pos e.pos n.pos⟩ _ _
      (PurCompactSupport.ramifiedMap l E.carrier L.carrier i e he n) (fun _ ↦ rfl)
  | reduction E n =>
    obtain ⟨n, hn⟩ := n
    cases n with
    | zero => omega
    | succ n => exact reductionRightMate l Ω D hl c operation left transport z E n
  | integral E L i =>
    exact completedRightMate l Ω D hl c operation left transport z E L i
  | identity s a h =>
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    have he := rightIdentity (operation s).adjunction (z.q a (.identity s a h))
      (z.mate l Ω a (.identity s a h)) (mateCounit l Ω z a (.identity s a h))
      (z.scalarIdentity a h (.identity s a h) true).iso
      (z.scalarIdentity a h (.identity s a h) false).iso
      (z.identityLeft a h (.identity s a h)) N
    have : IsIso ((z.mate l Ω a (.identity s a h)).app N ≫
        (operation s).G.map
          ((z.scalarIdentity a h (.identity s a h) false).iso.hom.app N)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((operation s).G.map
        ((z.scalarIdentity a h (.identity s a h) false).iso.hom.app N))
  | comp a b d h ha hb iha ihb =>
    let := iha
    let := ihb
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    have he := mateComposite l Ω z a b d h ha hb (.comp a b d h ha hb) N
    have : IsIso ((z.scalarComposition a b d h ha hb (.comp a b d h ha hb) true).iso.hom.app
        ((operation _).G.obj N) ≫ (z.mate l Ω d (.comp a b d h ha hb)).app N) := by
      rw [← he]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((z.scalarComposition a b d h ha hb (.comp a b d h ha hb) true).iso.hom.app
        ((operation _).G.obj N)) _

end WeilConjectures.ExceptionalIntegralScalar
