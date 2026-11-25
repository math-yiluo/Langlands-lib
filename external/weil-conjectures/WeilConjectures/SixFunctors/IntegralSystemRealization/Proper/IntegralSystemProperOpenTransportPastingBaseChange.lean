/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemBridgeExchange
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemBridgeOpenBaseChange
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting

/-! # Canonical proper/open base-change transport

Source: Stacks 0F7F and blueprint fix-prop-coherence. The cube is transported using
its six individual face comparisons and the supplied canonical bridge equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def bridgePair {C D K : Type*} [Category C] [Category D] [Category K]
    {F F' : C ⥤ D} {G G' : D ⥤ K} (e : F ≅ F') (f : G ≅ G') :
    F ⋙ G ≅ F' ⋙ G' :=
  Functor.isoWhiskerLeft F f ≪≫ Functor.isoWhiskerRight e G'

private theorem bridgePair_app {C D K : Type*} [Category C] [Category D] [Category K]
    {F F' : C ⥤ D} {G G' : D ⥤ K} (e : F ≅ F') (f : G ≅ G') (M : C) :
    (bridgePair e f).hom.app M = f.hom.app (F.obj M) ≫ G'.map (e.hom.app M) := rfl

private theorem bridgeLeft {B C D : Type*} [Category B] [Category C] [Category D]
    {H H' : B ⥤ C} {F F' G G' : C ⥤ D}
    (eH : H ≅ H') (eF : F ≅ F') (eG : G ≅ G')
    (α : F ⟶ G) (α' : F' ⟶ G') (h : α ≫ eG.hom = eF.hom ≫ α') :
    Functor.whiskerLeft H α ≫ (bridgePair eH eG).hom =
      (bridgePair eH eF).hom ≫ Functor.whiskerLeft H' α' := by
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, bridgePair_app]
  have hh := congr_app h (H.obj M)
  simp only [NatTrans.comp_app] at hh
  rw [← Category.assoc, hh]
  simp only [Category.assoc]
  rw [← α'.naturality]

private theorem bridgeRight {B C D : Type*} [Category B] [Category C] [Category D]
    {F F' G G' : B ⥤ C} {H H' : C ⥤ D}
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H')
    (α : F ⟶ G) (α' : F' ⟶ G') (h : α ≫ eG.hom = eF.hom ≫ α') :
    Functor.whiskerRight α H ≫ (bridgePair eG eH).hom =
      (bridgePair eF eH).hom ≫ Functor.whiskerRight α' H' := by
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, bridgePair_app]
  rw [← Category.assoc, eH.hom.naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← NatTrans.comp_app, h]
  simp only [NatTrans.comp_app, Functor.map_comp]

private theorem bridgePath {C : Type*} [Category C]
    {A B D K A' B' D' K' : C}
    {f : A ⟶ B} {g : B ⟶ D} {h : D ⟶ K}
    {f' : A' ⟶ B'} {g' : B' ⟶ D'} {h' : D' ⟶ K'}
    {s : A ⟶ A'} {t : B ⟶ B'} {v : D ⟶ D'} {w : K ⟶ K'}
    (hf : f ≫ t = s ≫ f') (hg : g ≫ v = t ≫ g') (hh : h ≫ w = v ≫ h') :
    (f ≫ g ≫ h) ≫ w = s ≫ (f' ≫ g' ≫ h') := by
  calc
    (f ≫ g ≫ h) ≫ w = f ≫ g ≫ (h ≫ w) := by simp only [Category.assoc]
    _ = f ≫ g ≫ (v ≫ h') := by rw [hh]
    _ = f ≫ (g ≫ v) ≫ h' := by simp only [Category.assoc]
    _ = f ≫ (t ≫ g') ≫ h' := by rw [hg]
    _ = (f ≫ t) ≫ g' ≫ h' := by simp only [Category.assoc]
    _ = (s ≫ f') ≫ g' ≫ h' := by rw [hf]
    _ = s ≫ (f' ≫ g' ≫ h') := by simp only [Category.assoc]

-- Transport a cube of functors through the twelve edge isomorphisms.
-- All calculations are generic, so the system constructions stay folded.
private theorem bridgeCube
    {A B C D A₁ B₁ C₁ D₁ : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A₁] [Category B₁] [Category C₁] [Category D₁]
    {R R' : A ⥤ C} {S S' : B ⥤ D} {J J' : A ⥤ B} {K K' : C ⥤ D}
    {R₁ R₁' : A₁ ⥤ C₁} {S₁ S₁' : B₁ ⥤ D₁}
    {J₁ J₁' : A₁ ⥤ B₁} {K₁ K₁' : C₁ ⥤ D₁}
    {Pa Pa' : B ⥤ B₁} {Pb Pb' : D ⥤ D₁}
    {Pc Pc' : C ⥤ C₁} {Pd Pd' : A ⥤ A₁}
    (er : R ≅ R') (es : S ≅ S') (ej : J ≅ J') (ek : K ≅ K')
    (er₁ : R₁ ≅ R₁') (es₁ : S₁ ≅ S₁') (ej₁ : J₁ ≅ J₁') (ek₁ : K₁ ≅ K₁')
    (ea : Pa ≅ Pa') (eb : Pb ≅ Pb') (ec : Pc ≅ Pc') (ed : Pd ≅ Pd')
    (γ : R ⋙ K ⟶ J ⋙ S) (γ' : R' ⋙ K' ⟶ J' ⋙ S')
    (δ : R₁ ⋙ K₁ ⟶ J₁ ⋙ S₁) (δ' : R₁' ⋙ K₁' ⟶ J₁' ⋙ S₁')
    (e : S ⋙ Pb ⟶ Pa ⋙ S₁) (e' : S' ⋙ Pb' ⟶ Pa' ⋙ S₁')
    (f : R ⋙ Pc ⟶ Pd ⋙ R₁) (f' : R' ⋙ Pc' ⟶ Pd' ⋙ R₁')
    (β : J ⋙ Pa ⟶ Pd ⋙ J₁) (β' : J' ⋙ Pa' ⟶ Pd' ⋙ J₁')
    (χ : K ⋙ Pb ⟶ Pc ⋙ K₁) (χ' : K' ⋙ Pb' ⟶ Pc' ⋙ K₁')
    (hγ : ∀ M, γ.app M ≫ es.hom.app (J.obj M) ≫ S'.map (ej.hom.app M) =
      ek.hom.app (R.obj M) ≫ K'.map (er.hom.app M) ≫ γ'.app M)
    (hδ : ∀ M, δ.app M ≫ es₁.hom.app (J₁.obj M) ≫ S₁'.map (ej₁.hom.app M) =
      ek₁.hom.app (R₁.obj M) ≫ K₁'.map (er₁.hom.app M) ≫ δ'.app M)
    (he : ∀ N, e.app N ≫ es₁.hom.app (Pa.obj N) ≫ S₁'.map (ea.hom.app N) =
      eb.hom.app (S.obj N) ≫ Pb'.map (es.hom.app N) ≫ e'.app N)
    (hf : ∀ N, f.app N ≫ er₁.hom.app (Pd.obj N) ≫ R₁'.map (ed.hom.app N) =
      ec.hom.app (R.obj N) ≫ Pc'.map (er.hom.app N) ≫ f'.app N)
    (hβ : ∀ M, β.app M ≫ ej₁.hom.app (Pd.obj M) ≫ J₁'.map (ed.hom.app M) =
      ea.hom.app (J.obj M) ≫ Pa'.map (ej.hom.app M) ≫ β'.app M)
    (hχ : ∀ N, χ.app N ≫ ek₁.hom.app (Pc.obj N) ≫ K₁'.map (ec.hom.app N) =
      eb.hom.app (K.obj N) ≫ Pb'.map (ek.hom.app N) ≫ χ'.app N)
    (M : A)
    (hi : Pb'.map (γ'.app M) ≫ e'.app (J'.obj M) ≫ S₁'.map (β'.app M) =
      χ'.app (R'.obj M) ≫ K₁'.map (f'.app M) ≫ δ'.app (Pd'.obj M)) :
    Pb.map (γ.app M) ≫ e.app (J.obj M) ≫ S₁.map (β.app M) =
      χ.app (R.obj M) ≫ K₁.map (f.app M) ≫ δ.app (Pd.obj M) := by
  have hγ₀ : γ ≫ (bridgePair ej es).hom = (bridgePair er ek).hom ≫ γ' := by
    ext N
    simpa only [NatTrans.comp_app, bridgePair_app, Category.assoc] using hγ N
  have hδ₀ : δ ≫ (bridgePair ej₁ es₁).hom = (bridgePair er₁ ek₁).hom ≫ δ' := by
    ext N
    simpa only [NatTrans.comp_app, bridgePair_app, Category.assoc] using hδ N
  have he₀ : e ≫ (bridgePair ea es₁).hom = (bridgePair es eb).hom ≫ e' := by
    ext N
    simpa only [NatTrans.comp_app, bridgePair_app, Category.assoc] using he N
  have hf₀ : f ≫ (bridgePair ed er₁).hom = (bridgePair er ec).hom ≫ f' := by
    ext N
    simpa only [NatTrans.comp_app, bridgePair_app, Category.assoc] using hf N
  have hβ₀ : β ≫ (bridgePair ed ej₁).hom = (bridgePair ej ea).hom ≫ β' := by
    ext N
    simpa only [NatTrans.comp_app, bridgePair_app, Category.assoc] using hβ N
  have hχ₀ : χ ≫ (bridgePair ec ek₁).hom = (bridgePair ek eb).hom ≫ χ' := by
    ext N
    simpa only [NatTrans.comp_app, bridgePair_app, Category.assoc] using hχ N
  have hG := congr_app (bridgeRight _ _ eb _ _ hγ₀) M
  have hP := congr_app (bridgeLeft ej _ _ _ _ he₀) M
  have hK := congr_app (bridgeRight _ _ es₁ _ _ hβ₀) M
  have hI := congr_app (bridgeLeft er _ _ _ _ hχ₀) M
  have hR := congr_app (bridgeRight _ _ ek₁ _ _ hf₀) M
  have hG₁ := congr_app (bridgeLeft ed _ _ _ _ hδ₀) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at hG hP hK hI hR hG₁
  let src := bridgePair (bridgePair er ek) eb
  let midL₁ := bridgePair (bridgePair ej es) eb
  let midL₂ := bridgePair (bridgePair ej ea) es₁
  let midR₁ := bridgePair (bridgePair er ec) ek₁
  let midR₂ := bridgePair (bridgePair ed er₁) ek₁
  let tgt := bridgePair (bridgePair ed ej₁) es₁
  have hL := bridgePath (s := src.hom.app M) (t := midL₁.hom.app M)
    (v := midL₂.hom.app M) (w := tgt.hom.app M) hG
    (by simpa only [midL₁, midL₂, bridgePair_app, Functor.map_comp,
          Functor.comp_obj, Functor.comp_map, Category.assoc] using hP) hK
  have hRhs := bridgePath (s := src.hom.app M) (t := midR₁.hom.app M)
    (v := midR₂.hom.app M) (w := tgt.hom.app M)
    (by simpa only [src, midR₁, bridgePair_app, Functor.map_comp,
          Functor.comp_obj, Functor.comp_map, Category.assoc] using hI) hR
    (by simpa only [midR₂, tgt, bridgePair_app, Functor.map_comp,
          Functor.comp_obj, Functor.comp_map, Category.assoc] using hG₁)
  apply (cancel_mono (tgt.hom.app M)).1
  exact hL.trans ((congrArg (fun q ↦ src.hom.app M ≫ q) hi).trans hRhs.symm)

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  pullbackTensorSequenceDerived properExchange CanonicalBridge.pull CanonicalBridge.push
  CanonicalBridge.shriek ProEtale.SemilinearProperOpen.gamma
  ProEtale.SemilinearProperOpen.exchange ProEtale.SemilinearProperOpen.beta
  ProEtale.SemilinearProperOpen.P ProEtale.SemilinearProperOpen.R
  ProEtale.SemilinearProperOpen.J
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftAdjoint
  Functor.mapDerivedCategoryNatIso
  DerivedCategory.Q Functor.mapDerivedCategoryFactors

private structure CubeData
    (A B C D A₁ B₁ C₁ D₁ : Type*)
    [Category A] [Category B] [Category C] [Category D]
    [Category A₁] [Category B₁] [Category C₁] [Category D₁] where
  R : A ⥤ C
  S : B ⥤ D
  J : A ⥤ B
  K : C ⥤ D
  R₁ : A₁ ⥤ C₁
  S₁ : B₁ ⥤ D₁
  J₁ : A₁ ⥤ B₁
  K₁ : C₁ ⥤ D₁
  Pa : B ⥤ B₁
  Pb : D ⥤ D₁
  Pc : C ⥤ C₁
  Pd : A ⥤ A₁
  γ : R ⋙ K ⟶ J ⋙ S
  δ : R₁ ⋙ K₁ ⟶ J₁ ⋙ S₁
  e : S ⋙ Pb ⟶ Pa ⋙ S₁
  f : R ⋙ Pc ⟶ Pd ⋙ R₁
  β : J ⋙ Pa ⟶ Pd ⋙ J₁
  χ : K ⋙ Pb ⟶ Pc ⋙ K₁

private structure CubeData.Comm
    {A B C D A₁ B₁ C₁ D₁ : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A₁] [Category B₁] [Category C₁] [Category D₁]
    (q : CubeData A B C D A₁ B₁ C₁ D₁) (M : A) : Prop where
  equal :
    q.Pb.map (q.γ.app M) ≫ q.e.app (q.J.obj M) ≫ q.S₁.map (q.β.app M) =
      q.χ.app (q.R.obj M) ≫ q.K₁.map (q.f.app M) ≫ q.δ.app (q.Pd.obj M)

private structure CommutingCube
    (A B C D A₁ B₁ C₁ D₁ : Type*)
    [Category A] [Category B] [Category C] [Category D]
    [Category A₁] [Category B₁] [Category C₁] [Category D₁] where
  data : CubeData A B C D A₁ B₁ C₁ D₁
  law : ∀ M, data.Comm M

private theorem CubeData.comm_explicit
    {A B C D A₁ B₁ C₁ D₁ : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A₁] [Category B₁] [Category C₁] [Category D₁]
    (q : CubeData A B C D A₁ B₁ C₁ D₁) (M : A) :
    q.Comm M → q.Pb.map (q.γ.app M) ≫ q.e.app (q.J.obj M) ≫ q.S₁.map (q.β.app M) =
      q.χ.app (q.R.obj M) ≫ q.K₁.map (q.f.app M) ≫ q.δ.app (q.Pd.obj M) :=
  fun h => h.equal

private theorem CubeData.comm_mk
    {A B C D A₁ B₁ C₁ D₁ : Type*}
    [catA : Category A] [catB : Category B] [catC : Category C] [catD : Category D]
    [catA₁ : Category A₁] [catB₁ : Category B₁] [catC₁ : Category C₁] [catD₁ : Category D₁]
    {R : A ⥤ C} {S : B ⥤ D} {J : A ⥤ B} {K : C ⥤ D}
    {R₁ : A₁ ⥤ C₁} {S₁ : B₁ ⥤ D₁} {J₁ : A₁ ⥤ B₁} {K₁ : C₁ ⥤ D₁}
    {Pa : B ⥤ B₁} {Pb : D ⥤ D₁} {Pc : C ⥤ C₁} {Pd : A ⥤ A₁}
    (γ : R ⋙ K ⟶ J ⋙ S) (δ : R₁ ⋙ K₁ ⟶ J₁ ⋙ S₁)
    (e : S ⋙ Pb ⟶ Pa ⋙ S₁) (f : R ⋙ Pc ⟶ Pd ⋙ R₁)
    (β : J ⋙ Pa ⟶ Pd ⋙ J₁) (χ : K ⋙ Pb ⟶ Pc ⋙ K₁) (M : A) :
    (CubeData.mk R S J K R₁ S₁ J₁ K₁ Pa Pb Pc Pd γ δ e f β χ).Comm M ↔
      Pb.map (γ.app M) ≫ e.app (J.obj M) ≫ S₁.map (β.app M) =
        χ.app (R.obj M) ≫ K₁.map (f.app M) ≫ δ.app (Pd.obj M) := ⟨fun h ↦ h.equal, fun h ↦ ⟨h⟩⟩

private theorem bridgeCubeData
    {A B C D A₁ B₁ C₁ D₁ : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A₁] [Category B₁] [Category C₁] [Category D₁]
    (first second : CubeData A B C D A₁ B₁ C₁ D₁)
    (er : first.R ≅ second.R)
    (es : first.S ≅ second.S)
    (ej : first.J ≅ second.J)
    (ek : first.K ≅ second.K)
    (er₁ : first.R₁ ≅ second.R₁)
    (es₁ : first.S₁ ≅ second.S₁)
    (ej₁ : first.J₁ ≅ second.J₁)
    (ek₁ : first.K₁ ≅ second.K₁)
    (ea : first.Pa ≅ second.Pa)
    (eb : first.Pb ≅ second.Pb)
    (ec : first.Pc ≅ second.Pc)
    (ed : first.Pd ≅ second.Pd)
    (hγ : ∀ M, first.γ.app M ≫ es.hom.app (first.J.obj M) ≫ second.S.map (ej.hom.app M) =
      ek.hom.app (first.R.obj M) ≫ second.K.map (er.hom.app M) ≫ second.γ.app M)
    (hδ : ∀ M, first.δ.app M ≫ es₁.hom.app (first.J₁.obj M) ≫ second.S₁.map (ej₁.hom.app M) =
      ek₁.hom.app (first.R₁.obj M) ≫ second.K₁.map (er₁.hom.app M) ≫ second.δ.app M)
    (he : ∀ N, first.e.app N ≫ es₁.hom.app (first.Pa.obj N) ≫ second.S₁.map (ea.hom.app N) =
      eb.hom.app (first.S.obj N) ≫ second.Pb.map (es.hom.app N) ≫ second.e.app N)
    (hf : ∀ N, first.f.app N ≫ er₁.hom.app (first.Pd.obj N) ≫ second.R₁.map (ed.hom.app N) =
      ec.hom.app (first.R.obj N) ≫ second.Pc.map (er.hom.app N) ≫ second.f.app N)
    (hβ : ∀ M, first.β.app M ≫ ej₁.hom.app (first.Pd.obj M) ≫ second.J₁.map (ed.hom.app M) =
      ea.hom.app (first.J.obj M) ≫ second.Pa.map (ej.hom.app M) ≫ second.β.app M)
    (hχ : ∀ N, first.χ.app N ≫ ek₁.hom.app (first.Pc.obj N) ≫ second.K₁.map (ec.hom.app N) =
      eb.hom.app (first.K.obj N) ≫ second.Pb.map (ek.hom.app N) ≫ second.χ.app N)
    (M : A)
    (hi : second.Comm M) : first.Comm M := by
  exact ⟨bridgeCube er es ej ek er₁ es₁ ej₁ ek₁ ea eb ec ed
    first.γ second.γ first.δ second.δ first.e second.e first.f second.f
    first.β second.β first.χ second.χ hγ hδ he hf hβ hχ M hi.equal⟩

private structure CubeBridge
    {A B C D A₁ B₁ C₁ D₁ : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A₁] [Category B₁] [Category C₁] [Category D₁]
    (first second : CubeData A B C D A₁ B₁ C₁ D₁) where
  er : first.R ≅ second.R
  es : first.S ≅ second.S
  ej : first.J ≅ second.J
  ek : first.K ≅ second.K
  er₁ : first.R₁ ≅ second.R₁
  es₁ : first.S₁ ≅ second.S₁
  ej₁ : first.J₁ ≅ second.J₁
  ek₁ : first.K₁ ≅ second.K₁
  ea : first.Pa ≅ second.Pa
  eb : first.Pb ≅ second.Pb
  ec : first.Pc ≅ second.Pc
  ed : first.Pd ≅ second.Pd
  hγ : ∀ M, first.γ.app M ≫ es.hom.app (first.J.obj M) ≫ second.S.map (ej.hom.app M) =
    ek.hom.app (first.R.obj M) ≫ second.K.map (er.hom.app M) ≫ second.γ.app M
  hδ : ∀ M, first.δ.app M ≫ es₁.hom.app (first.J₁.obj M) ≫ second.S₁.map (ej₁.hom.app M) =
    ek₁.hom.app (first.R₁.obj M) ≫ second.K₁.map (er₁.hom.app M) ≫ second.δ.app M
  he : ∀ N, first.e.app N ≫ es₁.hom.app (first.Pa.obj N) ≫ second.S₁.map (ea.hom.app N) =
    eb.hom.app (first.S.obj N) ≫ second.Pb.map (es.hom.app N) ≫ second.e.app N
  hf : ∀ N, first.f.app N ≫ er₁.hom.app (first.Pd.obj N) ≫ second.R₁.map (ed.hom.app N) =
    ec.hom.app (first.R.obj N) ≫ second.Pc.map (er.hom.app N) ≫ second.f.app N
  hβ : ∀ M, first.β.app M ≫ ej₁.hom.app (first.Pd.obj M) ≫ second.J₁.map (ed.hom.app M) =
    ea.hom.app (first.J.obj M) ≫ second.Pa.map (ej.hom.app M) ≫ second.β.app M
  hχ : ∀ N, first.χ.app N ≫ ek₁.hom.app (first.Pc.obj N) ≫ second.K₁.map (ec.hom.app N) =
    eb.hom.app (first.K.obj N) ≫ second.Pb.map (ek.hom.app N) ≫ second.χ.app N

private theorem CubeBridge.comm
    {A B C D A₁ B₁ C₁ D₁ : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A₁] [Category B₁] [Category C₁] [Category D₁]
    {first second : CubeData A B C D A₁ B₁ C₁ D₁}
    (z : CubeBridge first second) (M : A) (hi : second.Comm M) : first.Comm M := by
  exact bridgeCubeData first second z.er z.es z.ej z.ek z.er₁ z.es₁ z.ej₁ z.ek₁
    z.ea z.eb z.ec z.ed z.hγ z.hδ z.he z.hf z.hβ z.hχ M hi

private def intrinsicCube
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X_V X_W X_S X_T X_V₁ X_W₁ X_S₁ X_T₁ : Scheme.{u}}
      (k : X_V ⟶ X_W) (i : X_S ⟶ X_T) (r : X_V ⟶ X_S) (p : X_W ⟶ X_T)
      (k₁ : X_V₁ ⟶ X_W₁) (i₁ : X_S₁ ⟶ X_T₁) (r₁ : X_V₁ ⟶ X_S₁) (p₁ : X_W₁ ⟶ X_T₁)
      (aa : X_W₁ ⟶ X_W) (bb : X_T₁ ⟶ X_T) (cc : X_S₁ ⟶ X_S) (d : X_V₁ ⟶ X_V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (_sp : IsPullback aa p₁ p bb) (_sr : IsPullback d r₁ r cc) :
    CubeData
      (ProEtale.SemilinearProperOpen.Derived C τ X_V)
      (ProEtale.SemilinearProperOpen.Derived C τ X_W)
      (ProEtale.SemilinearProperOpen.Derived C τ X_S)
      (ProEtale.SemilinearProperOpen.Derived C τ X_T)
      (ProEtale.SemilinearProperOpen.Derived C τ X_V₁)
      (ProEtale.SemilinearProperOpen.Derived C τ X_W₁)
      (ProEtale.SemilinearProperOpen.Derived C τ X_S₁)
      (ProEtale.SemilinearProperOpen.Derived C τ X_T₁) where
  R := ProEtale.SemilinearProperOpen.R C τ r
  S := ProEtale.SemilinearProperOpen.R C τ p
  J := ProEtale.SemilinearProperOpen.J C τ k
  K := ProEtale.SemilinearProperOpen.J C τ i
  R₁ := ProEtale.SemilinearProperOpen.R C τ r₁
  S₁ := ProEtale.SemilinearProperOpen.R C τ p₁
  J₁ := ProEtale.SemilinearProperOpen.J C τ k₁
  K₁ := ProEtale.SemilinearProperOpen.J C τ i₁
  Pa := ProEtale.SemilinearProperOpen.P C τ aa
  Pb := ProEtale.SemilinearProperOpen.P C τ bb
  Pc := ProEtale.SemilinearProperOpen.P C τ cc
  Pd := ProEtale.SemilinearProperOpen.P C τ d
  γ := ProEtale.SemilinearProperOpen.gamma C τ k r p i h
  δ := ProEtale.SemilinearProperOpen.gamma C τ k₁ r₁ p₁ i₁ h₁
  e := ProEtale.SemilinearProperOpen.exchange C τ aa p₁ p bb wp
  f := ProEtale.SemilinearProperOpen.exchange C τ d r₁ r cc wr
  β := (ProEtale.SemilinearProperOpen.beta C τ d k₁ k aa wk sk).hom
  χ := (ProEtale.SemilinearProperOpen.beta C τ cc i₁ i bb wi si).hom

private theorem intrinsicCube_comm
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X_V X_W X_S X_T X_V₁ X_W₁ X_S₁ X_T₁ : Scheme.{u}}
      (k : X_V ⟶ X_W) (i : X_S ⟶ X_T) (r : X_V ⟶ X_S) (p : X_W ⟶ X_T)
      (k₁ : X_V₁ ⟶ X_W₁) (i₁ : X_S₁ ⟶ X_T₁) (r₁ : X_V₁ ⟶ X_S₁) (p₁ : X_W₁ ⟶ X_T₁)
      (aa : X_W₁ ⟶ X_W) (bb : X_T₁ ⟶ X_T) (cc : X_S₁ ⟶ X_S) (d : X_V₁ ⟶ X_V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (sp : IsPullback aa p₁ p bb) (sr : IsPullback d r₁ r cc)
    (M : ProEtale.SemilinearProperOpen.Derived C τ X_V) :
    (intrinsicCube C τ k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr).Comm M := by
  apply (CubeData.comm_mk
    (ProEtale.SemilinearProperOpen.gamma C τ k r p i h)
    (ProEtale.SemilinearProperOpen.gamma C τ k₁ r₁ p₁ i₁ h₁)
    (ProEtale.SemilinearProperOpen.exchange C τ aa p₁ p bb wp)
    (ProEtale.SemilinearProperOpen.exchange C τ d r₁ r cc wr)
    (ProEtale.SemilinearProperOpen.beta C τ d k₁ k aa wk sk).hom
    (ProEtale.SemilinearProperOpen.beta C τ cc i₁ i bb wi si).hom M).2
  exact (ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting C τ).2.2
    k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr M

private def intrinsicCommutingCube
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X_V X_W X_S X_T X_V₁ X_W₁ X_S₁ X_T₁ : Scheme.{u}}
      (k : X_V ⟶ X_W) (i : X_S ⟶ X_T) (r : X_V ⟶ X_S) (p : X_W ⟶ X_T)
      (k₁ : X_V₁ ⟶ X_W₁) (i₁ : X_S₁ ⟶ X_T₁) (r₁ : X_V₁ ⟶ X_S₁) (p₁ : X_W₁ ⟶ X_T₁)
      (aa : X_W₁ ⟶ X_W) (bb : X_T₁ ⟶ X_T) (cc : X_S₁ ⟶ X_S) (d : X_V₁ ⟶ X_V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (sp : IsPullback aa p₁ p bb) (sr : IsPullback d r₁ r cc) :
    CommutingCube
      (ProEtale.SemilinearProperOpen.Derived C τ X_V)
      (ProEtale.SemilinearProperOpen.Derived C τ X_W)
      (ProEtale.SemilinearProperOpen.Derived C τ X_S)
      (ProEtale.SemilinearProperOpen.Derived C τ X_T)
      (ProEtale.SemilinearProperOpen.Derived C τ X_V₁)
      (ProEtale.SemilinearProperOpen.Derived C τ X_W₁)
      (ProEtale.SemilinearProperOpen.Derived C τ X_S₁)
      (ProEtale.SemilinearProperOpen.Derived C τ X_T₁) where
  data := intrinsicCube C τ k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr
  law := intrinsicCube_comm C τ k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr

private def canonicalCommutingCube
    {X_V X_W X_S X_T X_V₁ X_W₁ X_S₁ X_T₁ : Scheme.{u}}
      (k : X_V ⟶ X_W) (i : X_S ⟶ X_T) (r : X_V ⟶ X_S) (p : X_W ⟶ X_T)
      (k₁ : X_V₁ ⟶ X_W₁) (i₁ : X_S₁ ⟶ X_T₁) (r₁ : X_V₁ ⟶ X_S₁) (p₁ : X_W₁ ⟶ X_T₁)
      (aa : X_W₁ ⟶ X_W) (bb : X_T₁ ⟶ X_T) (cc : X_S₁ ⟶ X_S) (d : X_V₁ ⟶ X_V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (sp : IsPullback aa p₁ p bb) (sr : IsPullback d r₁ r cc) :
    CommutingCube
      (coefficientSequenceDerived l E X_V)
      (coefficientSequenceDerived l E X_W)
      (coefficientSequenceDerived l E X_S)
      (coefficientSequenceDerived l E X_T)
      (coefficientSequenceDerived l E X_V₁)
      (coefficientSequenceDerived l E X_W₁)
      (coefficientSequenceDerived l E X_S₁)
      (coefficientSequenceDerived l E X_T₁) :=
  intrinsicCommutingCube (scalarRings l E) (scalarTransitions l E)
    k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr

private def canonicalCube
    {X_V X_W X_S X_T X_V₁ X_W₁ X_S₁ X_T₁ : Scheme.{u}}
      (k : X_V ⟶ X_W) (i : X_S ⟶ X_T) (r : X_V ⟶ X_S) (p : X_W ⟶ X_T)
      (k₁ : X_V₁ ⟶ X_W₁) (i₁ : X_S₁ ⟶ X_T₁) (r₁ : X_V₁ ⟶ X_S₁) (p₁ : X_W₁ ⟶ X_T₁)
      (aa : X_W₁ ⟶ X_W) (bb : X_T₁ ⟶ X_T) (cc : X_S₁ ⟶ X_S) (d : X_V₁ ⟶ X_V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (sp : IsPullback aa p₁ p bb) (sr : IsPullback d r₁ r cc) :
    CubeData
      (coefficientSequenceDerived l E X_V)
      (coefficientSequenceDerived l E X_W)
      (coefficientSequenceDerived l E X_S)
      (coefficientSequenceDerived l E X_T)
      (coefficientSequenceDerived l E X_V₁)
      (coefficientSequenceDerived l E X_W₁)
      (coefficientSequenceDerived l E X_S₁)
      (coefficientSequenceDerived l E X_T₁) :=
  (canonicalCommutingCube l E
    k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr).data

private def originalCube
    (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p)
    {X_V X_W X_S X_T X_V₁ X_W₁ X_S₁ X_T₁ : Scheme.{u}}
      (k : X_V ⟶ X_W) (i : X_S ⟶ X_T) (r : X_V ⟶ X_S) (p : X_W ⟶ X_T)
      (k₁ : X_V₁ ⟶ X_W₁) (i₁ : X_S₁ ⟶ X_T₁) (r₁ : X_V₁ ⟶ X_S₁) (p₁ : X_W₁ ⟶ X_T₁)
      (aa : X_W₁ ⟶ X_W) (bb : X_T₁ ⟶ X_T) (cc : X_S₁ ⟶ X_S) (d : X_V₁ ⟶ X_V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (_sp : IsPullback aa p₁ p bb) (_sr : IsPullback d r₁ r cc) :
    CubeData
      (coefficientSequenceDerived l E X_V)
      (coefficientSequenceDerived l E X_W)
      (coefficientSequenceDerived l E X_S)
      (coefficientSequenceDerived l E X_T)
      (coefficientSequenceDerived l E X_V₁)
      (coefficientSequenceDerived l E X_W₁)
      (coefficientSequenceDerived l E X_S₁)
      (coefficientSequenceDerived l E X_T₁) where
  R := Operations.push l E o r
  S := Operations.push l E o p
  J := Operations.shriek l E o k
  K := Operations.shriek l E o i
  R₁ := Operations.push l E o r₁
  S₁ := Operations.push l E o p₁
  J₁ := Operations.shriek l E o k₁
  K₁ := Operations.shriek l E o i₁
  Pa := pull l E aa
  Pb := pull l E bb
  Pc := pull l E cc
  Pd := pull l E d
  γ := gamma k r p i h
  δ := gamma k₁ r₁ p₁ i₁ h₁
  e := properExchange l E o c aa p₁ p bb wp
  f := properExchange l E o c d r₁ r cc wr
  β := (a.beta d k₁ k aa wk sk).hom
  χ := (a.beta cc i₁ i bb wi si).hom

private theorem canonicalCube_comm
    {X_V X_W X_S X_T X_V₁ X_W₁ X_S₁ X_T₁ : Scheme.{u}}
      (k : X_V ⟶ X_W) (i : X_S ⟶ X_T) (r : X_V ⟶ X_S) (p : X_W ⟶ X_T)
      (k₁ : X_V₁ ⟶ X_W₁) (i₁ : X_S₁ ⟶ X_T₁) (r₁ : X_V₁ ⟶ X_S₁) (p₁ : X_W₁ ⟶ X_T₁)
      (aa : X_W₁ ⟶ X_W) (bb : X_T₁ ⟶ X_T) (cc : X_S₁ ⟶ X_S) (d : X_V₁ ⟶ X_V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (sp : IsPullback aa p₁ p bb) (sr : IsPullback d r₁ r cc)
    (M : coefficientSequenceDerived l E X_V) :
    (canonicalCube l E k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr).Comm M :=
  (canonicalCommutingCube l E
    k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr).law M

private def canonicalCubeBridge
    (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p)
    (b : CanonicalBridge l E o)
    (canonical : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (gamma k r p i h).app M ≫
        (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M)
    {X_V X_W X_S X_T X_V₁ X_W₁ X_S₁ X_T₁ : Scheme.{u}}
      (k : X_V ⟶ X_W) (i : X_S ⟶ X_T) (r : X_V ⟶ X_S) (p : X_W ⟶ X_T)
      (k₁ : X_V₁ ⟶ X_W₁) (i₁ : X_S₁ ⟶ X_T₁) (r₁ : X_V₁ ⟶ X_S₁) (p₁ : X_W₁ ⟶ X_T₁)
      (aa : X_W₁ ⟶ X_W) (bb : X_T₁ ⟶ X_T) (cc : X_S₁ ⟶ X_S) (d : X_V₁ ⟶ X_V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (sp : IsPullback aa p₁ p bb) (sr : IsPullback d r₁ r cc) :
    CubeBridge
      (originalCube l E o c a gamma
        k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr)
      (canonicalCube l E k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr) where
  er := b.push l E r
  es := b.push l E p
  ej := b.shriek l E k
  ek := b.shriek l E i
  er₁ := b.push l E r₁
  es₁ := b.push l E p₁
  ej₁ := b.shriek l E k₁
  ek₁ := b.shriek l E i₁
  ea := b.pull l E aa
  eb := b.pull l E bb
  ec := b.pull l E cc
  ed := b.pull l E d
  hγ := canonical k r p i h
  hδ := canonical k₁ r₁ p₁ i₁ h₁
  he := integralSystemBridgeExchange l E o c b aa p₁ p bb wp
  hf := integralSystemBridgeExchange l E o c b d r₁ r cc wr
  hβ := integralSystemBridgeOpenBaseChange l E o c a b d k₁ k aa wk sk
  hχ := integralSystemBridgeOpenBaseChange l E o c a b cc i₁ i bb wi si

attribute [local irreducible] canonicalCube canonicalCubeBridge

-- Reify definitional conversions as congruence proofs. In particular, do not ask
-- the kernel to unfold a derived pullback map while comparing its arguments.
-- The pattern is also used by IntegralOrdinaryProperOpenSquare.typeCongruence.
private meta def transportCompObj (x : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let args := x.getAppArgs
  if x.isAppOf ``Functor.obj && args.size ≥ 2 then
    let f := args[args.size - 2]!
    if f.isAppOf ``Functor.comp then
      let fs := f.getAppArgs
      let h ← Lean.Meta.mkAppM ``Functor.comp_obj
        #[fs[fs.size - 2]!, fs.back!, args.back!]
      return some ((← Lean.Meta.inferType h).getAppArgs.back!,
        ← Lean.Meta.mkHEqOfEq h)
  return none

private meta partial def transportCongruence (x y : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let x := x.consumeMData
  let y := y.consumeMData
  if x == y then return ← Lean.Meta.mkHEqRefl x
  if let some (x', h) ← transportCompObj x then
    return ← Lean.Meta.mkAppM ``HEq.trans #[h, ← transportCongruence x' y]
  if let some (y', h) ← transportCompObj y then
    return ← Lean.Meta.mkAppM ``HEq.trans
      #[← transportCongruence x y', ← Lean.Meta.mkAppM ``HEq.symm #[h]]
  if (← Lean.Meta.isProof x) && (← Lean.Meta.isProof y) then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[x, y]
  if x.getAppFn == y.getAppFn && x.isApp && x.getAppNumArgs == y.getAppNumArgs then
    let thm ← Lean.Meta.mkHCongrWithArity x.getAppFn x.getAppNumArgs
    let mut args := #[]
    for a in x.getAppArgs, b in y.getAppArgs, kind in thm.argKinds do
      let h ← transportCongruence a b
      match kind with
      | .eq => args := args ++ #[a, b, ← Lean.Meta.mkEqOfHEq h]
      | .heq => args := args ++ #[a, b, h]
      | _ => throwError "Unexpected congruence argument"
    let h := Lean.mkAppN thm.proof args
    if (← Lean.Meta.inferType h).isHEq then return h
    return ← Lean.Meta.mkHEqOfEq h
  return ← Lean.Meta.mkHEqRefl x

/-- Base-change pasting for a gamma satisfying the canonical bridge equation.
Source: Stacks 0F7C, 0F7D and 0F7F; Zheng Lemma 4.10.
(blueprint: lem-sf-integral-system-proper-open-transport-pasting-basechange).

Proof: the supplied canonical equation identifies the top and bottom gamma maps
under the bridge. The one-square exchange and open-beta comparisons identify the
four other faces. Whisker these six equations, use naturality to regroup the
bridge maps, and paste the equations along both three-arrow paths. The intrinsic
base-change equation identifies the resulting paths. Cancel the common terminal
bridge isomorphism. The canonical bridge equation replaces the invalid earlier
quantifier over arbitrary gamma, which need not respect base change. -/
theorem integralSystemProperOpenTransportPastingBaseChange
    (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    (gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p)
    (b : CanonicalBridge l E o)
    (canonical : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (gamma k r p i h).app M ≫
        (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M) :
  ∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (aa : W₁ ⟶ W) (bb : T₁ ⟶ T) (cc : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (_sp : IsPullback aa p₁ p bb) (_sr : IsPullback d r₁ r cc) (M : System l E V),
      (pull l E bb).map ((gamma k r p i h).app M) ≫
          (properExchange l E o c aa p₁ p bb wp).app ((Operations.shriek l E o k).obj M) ≫
          (Operations.push l E o p₁).map ((a.beta d k₁ k aa wk sk).hom.app M) =
        (a.beta cc i₁ i bb wi si).hom.app ((Operations.push l E o r).obj M) ≫
          (Operations.shriek l E o i₁).map ((properExchange l E o c d r₁ r cc wr).app M) ≫
          (gamma k₁ r₁ p₁ i₁ h₁).app ((pull l E d).obj M) := by
  intro V W S T V₁ W₁ S₁ T₁ k i r p k₁ i₁ r₁ p₁ aa bb cc d
    _ _ _ _ _ _ _ _ _ _ _ _ h h₁ wk wi wp wr sk si sp sr M
  let q := originalCube l E o c a gamma
    k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr
  have hcub := (canonicalCubeBridge l E o c a gamma b canonical
    k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr).comm M
    (canonicalCube_comm l E k i r p k₁ i₁ r₁ p₁ aa bb cc d h h₁ wk wi wp wr sk si sp sr M)
  have hx := CubeData.comm_explicit q M hcub
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hx
      | Lean.throwError "missing transported cube equation"
    let source ← Lean.Meta.whnf hd.type
    let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
    let e ← Lean.Meta.mkEqOfHEq (← transportCongruence source target)
    let result ← Lean.Meta.mkAppM ``Eq.mp #[e, hd.toExpr]
    Lean.Elab.Tactic.closeMainGoal `exact result

end WeilConjectures.IntegralSystemRealization
