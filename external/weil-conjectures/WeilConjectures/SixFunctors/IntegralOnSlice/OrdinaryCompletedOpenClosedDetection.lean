/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionExact
import WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryCompletedLocalizationSequence
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Ordinary completed-coefficient module pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice

universe a b r

private theorem sliceModuleTransportDirect
    {C H : Type a} [Category.{b} C] [Category.{b} H]
    (J : GrothendieckTopology C) (K : GrothendieckTopology H)
    (e : C ≌ H) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J RingCat.{r}) (S : Sheaf K RingCat.{r})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{r} K J).obj R) :
    ∃ q : SheafOfModules.{r} R ≌ SheafOfModules.{r} S,
      q.functor = SheafOfModules.pushforward.{r} c.hom := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{r} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  let q : SheafOfModules.{r} R ≌ SheafOfModules.{r} S :=
    SheafOfModules.pushforwardPushforwardEquivalence.{r} e.symm c.hom ψ H₁ H₂
  exact ⟨q, rfl⟩

private theorem ordinaryOpenSliceComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X : Scheme.{t}} [CompactSpace X] [QuasiSeparatedSpace X]
    (V : X.ProEt) [CompactSpace V.left] [QuasiSeparatedSpace V.left]
    [IsOpenImmersion V.hom] :
    ∃ q : Mod l E V.left none ≌
        SheafOfModules.{max u (t + 1)}
          ((completedIntegralCoefficientSheafUnrestricted l E X).over V),
      Nonempty (ordinaryPull l E V.hom ⋙ q.functor ≅
        SheafOfModules.overFunctor.{max u (t + 1)}
          (completedIntegralCoefficientSheafUnrestricted l E X) V) := by
  have hc : IsIso (ordinaryCoefficientMap l E V.hom) := by
    have h := (qcqsOrdinaryRestrictionExact l E (S := V.left) (V := V.left) (T := X)
      (𝟙 V.left) V.hom).2
    have hcomp : (𝟙 V.left ≫ V.hom : V.left ⟶ X) = V.hom := Category.id_comp V.hom
    exact hcomp ▸ h
  let R := completedIntegralCoefficientSheafUnrestricted l E X
  let S := completedIntegralCoefficientSheafUnrestricted l E V.left
  let G : V.left.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ V.prop
  let : G.IsContinuous (ProEt.topology V.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap V.prop
  let : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology V.left) := ProEt.isContinuous_overPullback V.hom
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ V.hom V.prop trivial
  let b := a.sheafPushforwardContinuous (E := RingCat.{max u (t + 1)})
    (ProEt.topology V.left) (ProEt.topology X)
  let e := (Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} V.hom)).leftAdjointUniq b
  let c : S ≅ (G.sheafPushforwardContinuous RingCat.{max u (t + 1)}
      (ProEt.topology V.left) (ProEt.topology X)).obj R :=
    (asIso (ordinaryCoefficientMap l E V.hom)).symm ≪≫ e.app R
  let ψ := ordinaryCompletedRingMap l E V.hom
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ (proEtaleBaseChange V.hom).op.whiskerLeft c.hom.hom := by
    have h := Adjunction.unit_leftAdjointUniq_hom_app
      (Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} V.hom)) b R
    have hφ : ψ =
        (Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} V.hom)).unit.app R ≫
          (ordinaryRingPush.{t, u} V.hom).map (ordinaryCoefficientMap l E V.hom) := by
      exact (((Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} V.hom)).homEquiv
        _ _).apply_symm_apply ψ).symm
    have heq : b.unit.app R = ψ ≫ (ordinaryRingPush.{t, u} V.hom).map c.hom := by
      rw [hφ, Category.assoc, ← Functor.map_comp]
      have hc' : ordinaryCoefficientMap l E V.hom ≫ c.hom = e.hom.app R := by
        dsimp only [c, Iso.trans_hom, Iso.symm_hom, asIso_inv]
        rw [IsIso.hom_inv_id_assoc]
        rfl
      rw [hc']
      exact h.symm
    exact congrArg (fun f ↦ f.hom) heq
  have H₂ : c.hom.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext W
    apply (cancel_mono (c.hom.hom.app W)).mp
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.hom.naturality (a.unit.app W.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun t ↦ t.app (G.op.obj W)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj W))
      (c.hom.hom.app ((proEtaleBaseChange V.hom).op.obj (G.op.obj W)))
      (R.obj.map (G.map (a.unit.app W.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.hom.app W ≫ R.obj.map (𝟙 (G.op.obj W)) = c.hom.hom.app W
    rw [R.obj.map_id]
    exact Category.comp_id _
  let d := SheafOfModules.pushforwardPushforwardAdj a c.hom ψ H₁ H₂
  let z := (ordinaryAdjunction l E V.hom).leftAdjointUniq d
  have := ProEt.sliceDense X V
  have : ((ProEt.sliceEquiv X V).inverse ⋙ Over.forget V).IsContinuous
      (ProEt.topology V.left) (ProEt.topology X) :=
    Functor.isContinuous_comp _ _ _ ((ProEt.topology X).over V) _
  obtain ⟨q, hq⟩ := sliceModuleTransportDirect ((ProEt.topology X).over V)
    (ProEt.topology V.left) (ProEt.sliceEquiv X V) (R.over V) S c
  let k : SheafOfModules.overFunctor.{max u (t + 1)} R V ⋙ q.functor ≅
      SheafOfModules.pushforward.{max u (t + 1)} c.hom :=
    Functor.isoWhiskerLeft (SheafOfModules.overFunctor R V) (eqToIso hq) ≪≫
      SheafOfModules.pushforwardComp.{max u (t + 1)}
        (F := (ProEt.sliceEquiv X V).inverse) (G := Over.forget V)
        (R := R.over V) (R' := R) c.hom (𝟙 (R.over V)) ≪≫
      SheafOfModules.pushforwardCongr (by simp)
  refine ⟨q.symm, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight (z ≪≫ k.symm) q.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.overFunctor R V) q.unitIso.symm ≪≫
    Functor.rightUnitor _

/-- Complementary open and closed restrictions jointly detect module isomorphisms.
Source: Stacks, Pro-etale Cohomology, Tags 09AH, 09AG and 09BM.
(blueprint: lem-fix-ordinary-completed-open-closed-detection).
Proof: the finite-projection identifications of the completed coefficient rings
identify ordinaryPull along j and i with ringed inverse image with restricted
coefficients. Present the open inverse image as restriction to the localized site.
Slice restriction preserves limits, so the finite constant-sheaf identifications
pass to the completion and its projections. Uniqueness of the direct completed
ring map identifies this coefficient map with the one defining ordinaryPull;
uniqueness of left adjoints identifies the module functors.
Use the ringed open-closed construction in module universe max u (t+1): the site
has object size t+1, so module sheafification exists in that universe. Extension
by zero and the localization sequence are constructed by the same sheafification
of module presheaves as in the source, with no equality of coefficient and site
universes required. Its exactness proof is local and applies to these coefficients.
This construction supplies the exact sequence
0 -> j!j* M -> M -> i*i* M -> 0, with its actual unit and counit maps.
For a module morphism whose two restrictions are invertible, naturality gives a
map between the two short exact sequences. Its outer maps are invertible because
functors preserve isomorphisms. The short five lemma makes the middle map invertible.
The finite-projection identifications preserve scalar actions and hence transport
this conclusion to the specified ordinaryPull functors. If either piece is empty,
the same short exact sequence and argument apply. No derived category occurs. -/
theorem ordinaryCompletedOpenClosedDetection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S U Z : Scheme.{t})
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (j : U ⟶ S) (i : Z ⟶ S)
    [IsOpenImmersion j] [QuasiCompact j] [IsClosedImmersion i]
    (hcover : Set.range j.base ∪ Set.range i.base = Set.univ)
    (hdisj : Disjoint (Set.range j.base) (Set.range i.base)) :
    ∀ {M N : Mod l E S none} (f : M ⟶ N),
      IsIso ((ordinaryPull l E j).map f) →
      IsIso ((ordinaryPull l E i).map f) → IsIso f := by
  intro M N f hj hi
  let V := ProEt.mk j
  have : CompactSpace V.left := inferInstanceAs (CompactSpace U)
  have : QuasiSeparatedSpace V.left := inferInstanceAs (QuasiSeparatedSpace U)
  have : IsOpenImmersion V.hom := ‹IsOpenImmersion j›
  have : QuasiCompact V.hom := ‹QuasiCompact j›
  have hV : Set.range V.hom = (Set.range i)ᶜ := by
    ext x
    constructor
    · intro hx hi'
      exact Set.disjoint_left.mp hdisj hx hi'
    · intro hx
      have hh : x ∈ Set.range j.base ∪ Set.range i.base := by
        rw [hcover]
        trivial
      exact hh.resolve_right hx
  obtain ⟨q, ⟨e⟩⟩ := ordinaryOpenSliceComparison l E V
  let a := SheafOfModules.localizedSystemAdjunction.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E S) V
  let L := SheafOfModules.localizedSystemRestriction.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E S) V
  let T := SheafOfModules.localizedSystemExtension.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E S) V
  have : IsIso ((ordinaryPull l E j).map f) := hj
  have : IsIso ((ordinaryPull l E i).map f) := hi
  have : IsIso (L.map f) := by
    have hnat := e.hom.naturality f
    have : IsIso ((ordinaryPull l E V.hom).map f) := hj
    have : IsIso ((ordinaryPull l E V.hom ⋙ q.functor).map f) := by
      change IsIso (q.functor.map ((ordinaryPull l E V.hom).map f))
      infer_instance
    have heq : L.map f = e.inv.app M ≫
        (ordinaryPull l E V.hom ⋙ q.functor).map f ≫ e.hom.app N := by
      rw [hnat, Iso.inv_hom_id_app_assoc]
      rfl
    rw [heq]
    infer_instance
  have hs := ordinaryCompletedLocalizationSequence l E i V hV
  let C (P : Mod l E S none) : ShortComplex (Mod l E S none) :=
    ShortComplex.mk (a.counit.app P) ((ordinaryAdjunction l E i).unit.app P)
      ((hs P).2.2.toIsComplex.zero 0)
  have hC (P : Mod l E S none) : (C P).ShortExact :=
    { exact := ((ComposableArrows.mk₂ (a.counit.app P)
        ((ordinaryAdjunction l E i).unit.app P)).exact₂_iff
          (hs P).2.2.toIsComplex).1 (hs P).2.2
      mono_f := (hs P).1
      epi_g := (hs P).2.1 }
  let φ : C M ⟶ C N :=
    { τ₁ := T.map (L.map f)
      τ₂ := f
      τ₃ := (ordinaryPush l E i).map ((ordinaryPull l E i).map f)
      comm₁₂ := a.counit.naturality f
      comm₂₃ := (ordinaryAdjunction l E i).unit.naturality f }
  have : IsIso φ.τ₁ := inferInstanceAs (IsIso (T.map (L.map f)))
  have : IsIso φ.τ₃ := inferInstanceAs
    (IsIso ((ordinaryPush l E i).map ((ordinaryPull l E i).map f)))
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ (hC M) (hC N)

end WeilConjectures.IntegralOnSlice
