/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralSystemScalarCoreData

/-! # Normalized selected scalar comparison
Source: Zheng, Construction 4.1, Lemma 5.22, and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-system-selected-left-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite SheafOfModules
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem isoCast_heq {A B : Type*} [Category A] [Category B]
    {F F' G G' : A ⥤ B} (p : F = F') (q : G = G') (h : F' ≅ G') (K : A) :
    HEq ((eqToIso p ≪≫ h ≪≫ (eqToIso q).symm).hom.app K) (h.hom.app K) := by
  subst F' G'
  simp

private theorem liftSquare {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category B₀] [Category B₁] [Category B₂] [Category B₃]
    (I₀ : A₀ ⥤ B₀) (I₁ : A₁ ⥤ B₁) (I₂ : A₂ ⥤ B₂) (I₃ : A₃ ⥤ B₃)
    [I₃.Full] [I₃.Faithful]
    (A : A₀ ⥤ A₁) (B : A₁ ⥤ A₃) (R : A₀ ⥤ A₂) (S : A₂ ⥤ A₃)
    (TA : B₀ ⥤ B₁) (TB : B₁ ⥤ B₃) (TR : B₀ ⥤ B₂) (TS : B₂ ⥤ B₃)
    (hA : A ⋙ I₁ ≅ I₀ ⋙ TA) (hB : B ⋙ I₃ = I₁ ⋙ TB)
    (hR : R ⋙ I₂ = I₀ ⋙ TR) (hS : S ⋙ I₃ = I₂ ⋙ TS)
    (sq : TA ⋙ TB ≅ TR ⋙ TS) :
    ∃ q : A ⋙ B ≅ R ⋙ S, ∀ K : A₀,
      HEq (I₃.map (q.hom.app K))
        (TB.map (hA.hom.app K) ≫ sq.hom.app (I₀.obj K)) := by
  let p : (A ⋙ B) ⋙ I₃ = (A ⋙ I₁) ⋙ TB :=
    congrArg (fun F ↦ A ⋙ F) hB
  let q : (R ⋙ S) ⋙ I₃ = I₀ ⋙ (TR ⋙ TS) :=
    (congrArg (fun F ↦ R ⋙ F) hS).trans (congrArg (fun F ↦ F ⋙ TS) hR)
  let v : (A ⋙ I₁) ⋙ TB ≅ I₀ ⋙ (TR ⋙ TS) :=
    isoWhiskerRight hA TB ≪≫ isoWhiskerLeft I₀ sq
  let w := eqToIso p ≪≫ v ≪≫ (eqToIso q).symm
  refine ⟨Functor.fullyFaithfulCancelRight I₃ w, ?_⟩
  intro K
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  exact isoCast_heq p q v K

private theorem transportSelected {A B N M C D : Type*}
    [Category A] [Category B] [Category N] [Category M] [Category C] [Category D]
    (re : A ≌ N) (rl : B ≌ M) (S : A ⥤ B) (s : N ⥤ M)
    (m : M ⥤ D) (n : N ⥤ C) (R : A ⥤ C) (Bf : B ⥤ D) (Z : C ⥤ D)
    (core : S ⋙ rl.functor ≅ re.functor ⋙ s)
    (eL : Bf ≅ rl.functor ⋙ m) (eE : R ≅ re.functor ⋙ n)
    (sq : S ⋙ Bf ≅ R ⋙ Z) :
    ∃ q : s ⋙ m ≅ n ⋙ Z, ∀ K : A,
      eL.hom.app (S.obj K) ≫ m.map (core.hom.app K) ≫
        q.hom.app (re.functor.obj K) ≫ Z.map (eE.inv.app K) = sq.hom.app K := by
  let hpre : re.functor ⋙ (s ⋙ m) ≅ re.functor ⋙ (n ⋙ Z) :=
    isoWhiskerRight core.symm m ≪≫ isoWhiskerLeft S eL.symm ≪≫
      sq ≪≫ isoWhiskerRight eE Z
  let W := (Functor.whiskeringLeft A N D).obj re.functor
  let q : s ⋙ m ≅ n ⋙ Z := W.preimageIso hpre
  refine ⟨q, ?_⟩
  intro K
  have h : q.hom.app (re.functor.obj K) = hpre.hom.app K :=
    congr_app (W.map_preimage hpre.hom) K
  rw [h]
  dsimp only [hpre, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Iso.symm_hom]
  simp only [Category.assoc, ← m.map_comp_assoc, Iso.hom_inv_id_app,
    ← Z.map_comp, Z.map_id]
  change eL.hom.app (S.obj K) ≫ m.map (𝟙 _) ≫
    eL.inv.app (S.obj K) ≫ sq.hom.app K ≫ 𝟙 _ = _
  rw [m.map_id]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp, Category.comp_id, Iso.hom_inv_id_app_assoc]

/-- Construct the selected comparison with its tensor-square normalization.
Source: Zheng, Construction 4.1, Lemma 5.22, and Proposition 5.26.
Proof: at each ramified square and endpoint, Mates.finiteScalar_eq identifies the
two reduction functors and the finite scalar functor, after the full finite-Tor
inclusion, with the ambient derived scalar composites. Whisker the integral scalar
realization by the target reduction and compose with PurCompactSupport.tensorSquare;
lift this through the fully faithful finite-Tor inclusion (fullyFaithfulCancelRight),
its map being heterogeneously equal to the specified composite. Then precompose with
reconstruction over E: insert core.reduction inverse, the inverse reduction comparison
over L, the lifted square, and the reduction comparison over E. Precomposition by the
reconstruction equivalence is fully faithful, so this composite descends to a selected
comparison of functors (preimageIso). On reconstructed integral objects the inverse
factors cancel and the lifted-square equation gives the displayed balanced equation.
No faithfulness of finite evaluation is used.
(blueprint: lem-sf-exceptional-integral-system-selected-left-comparison). -/
theorem exceptionalIntegralSystemSelected
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
    (d : Mates l Ω c operation left)
    (red : ∀ (E : FieldStage.{u} l) (n : ℕ),
      ReductionMates l Ω D hl c operation left transport d E n)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (core : SystemScalarCore l Ω D hl c operation left transport d E L i)
    (selected_square : ∀ (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (T : Scheme.{u}),
    (PurCompactSupport.completedChange l E.carrier L.carrier i).map T ≫
        (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map T =
      (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map T ≫
        z.change.map T) :
    ∃ selected : (∀ (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool),
    core.scalar side ⋙ (transport.reconstruction L side).evaluation z.m ≅
      (transport.reconstruction E side).evaluation z.n ⋙
        (d.scalar z.change z.allowed side).functor),
      ∀ (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)),
    HEq ((finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
      (endpoint X Y side)).ι.map
        ((red L z.m).evaluation side |>.hom.app
            ((d.scalar (s := .integral E) (t := .integral L)
              (PurCompactSupport.completedChange l E.carrier L.carrier i)
              (Allowed.integral E L i) side).functor.obj K)) ≫
      (finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
        (endpoint X Y side)).ι.map
        (((transport.reconstruction L side).evaluation z.m).map ((core.reduction side).hom.app K) ≫
          (selected e he z side).hom.app
            ((transport.reconstruction E side).equivalence.functor.obj K) ≫
          (d.scalar z.change z.allowed side).functor.map
            (((red E z.n).evaluation side).inv.app K)))
      ((pbcDerivedExtend ((PurCompactSupport.reduction l L.carrier
          (z.m + 1) (Nat.succ_pos z.m)).map (endpoint X Y side))).map
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) side).realization.hom.app K) ≫
        (PurCompactSupport.tensorSquare
          ((PurCompactSupport.completedChange l E.carrier L.carrier i).map
            (endpoint X Y side)) (z.change.map (endpoint X Y side))
          ((PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map
            (endpoint X Y side))
          ((PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map
            (endpoint X Y side)) (selected_square e he z (endpoint X Y side))).hom.app K.obj) := by
  classical
  have hsquare (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool) :=
    liftSquare
      (RingStage.inclusion l Ω (endpoint X Y side) (.integral E))
      (RingStage.inclusion l Ω (endpoint X Y side) (.integral L))
      (RingStage.inclusion l Ω (endpoint X Y side)
        (.finite E ⟨z.n + 1, Nat.succ_pos z.n⟩))
      (RingStage.inclusion l Ω (endpoint X Y side)
        (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩))
      (d.scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).functor
      (d.scalar (s := .integral L) (t := .finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)
        (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m))
        (Allowed.reduction L ⟨z.m + 1, Nat.succ_pos z.m⟩) side).functor
      (d.scalar (s := .integral E) (t := .finite E ⟨z.n + 1, Nat.succ_pos z.n⟩)
        (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n))
        (Allowed.reduction E ⟨z.n + 1, Nat.succ_pos z.n⟩) side).functor
      (d.scalar z.change z.allowed side).functor
      (pbcDerivedExtend ((PurCompactSupport.completedChange l E.carrier L.carrier i).map
        (endpoint X Y side)))
      (pbcDerivedExtend ((PurCompactSupport.reduction l L.carrier
        (z.m + 1) (Nat.succ_pos z.m)).map (endpoint X Y side)))
      (pbcDerivedExtend ((PurCompactSupport.reduction l E.carrier
        (z.n + 1) (Nat.succ_pos z.n)).map (endpoint X Y side)))
      (pbcDerivedExtend (z.change.map (endpoint X Y side)))
      (d.scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).realization
      (d.finiteScalar_eq (s := .integral L) L ⟨z.m + 1, Nat.succ_pos z.m⟩
        (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m))
        (Allowed.reduction L ⟨z.m + 1, Nat.succ_pos z.m⟩) side)
      (d.finiteScalar_eq (s := .integral E) E ⟨z.n + 1, Nat.succ_pos z.n⟩
        (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n))
        (Allowed.reduction E ⟨z.n + 1, Nat.succ_pos z.n⟩) side)
      (d.finiteScalar_eq L ⟨z.m + 1, Nat.succ_pos z.m⟩ z.change z.allowed side)
      (PurCompactSupport.tensorSquare
        ((PurCompactSupport.completedChange l E.carrier L.carrier i).map
          (endpoint X Y side)) (z.change.map (endpoint X Y side))
        ((PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map
          (endpoint X Y side))
        ((PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map
          (endpoint X Y side)) (selected_square e he z (endpoint X Y side)))
  choose sq hsq using hsquare
  have hselected (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool) :=
    transportSelected (transport.reconstruction E side).equivalence
      (transport.reconstruction L side).equivalence _ (core.scalar side)
      ((transport.reconstruction L side).evaluation z.m)
      ((transport.reconstruction E side).evaluation z.n) _ _ _
      (core.reduction side) ((red L z.m).evaluation side)
      ((red E z.n).evaluation side) (sq e he z side)
  choose selected hselected using hselected
  refine ⟨selected, ?_⟩
  intro e he z side K
  rw [← Functor.map_comp, hselected e he z side K]
  exact hsq e he z side K

end WeilConjectures.ExceptionalIntegralScalar
