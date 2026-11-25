/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherenceData
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.TraceFormula.Sequence.SequenceScalarGeneratorInterchange
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # A component of strict quotient-system coherence

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe t u a v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  integralComparisonSequenceScalarModel
attribute [local instance 5000] coefficientSequenceEssentiallySmall
attribute [local instance 6000] HasDerivedCategory.standard
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  finiteSystemSequenceSmall finiteSystemSiteSmall
attribute [local irreducible] HasDerivedCategory.standard

private theorem exactComposition_fac
    {A B C : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    [Category C] [Abelian C] [HasDerivedCategory C]
    (p : A ⥤ B) (q : B ⥤ C) (r : A ⥤ C)
    [p.Additive] [q.Additive] [r.Additive]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (c : r ≅ p ⋙ q) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryNatIso c ≪≫ (Functor.mapDerivedCategoryCompIso p q).symm).hom.app
        (DerivedCategory.Q.obj P) ≫
      q.mapDerivedCategory.map (p.mapDerivedCategoryFactors.hom.app P) ≫
      q.mapDerivedCategoryFactors.hom.app ((p.mapHomologicalComplex (.up ℤ)).obj P) =
    r.mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) := by
  have hc := Functor.mapDerivedCategoryCompIso_fac p q P
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (p ⋙ q))
      (.up ℤ)).hom.app P = 𝟙 _ := rfl
  rw [hi] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hc]
  exact Functor.mapDerivedCategoryNatIso_fac c P

-- Pasting normalized squares only uses naturality and the displayed counit equations.
private theorem mixedPasting
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (p : A₀ ⥤ A₁) (q : A₁ ⥤ A₂) (r : A₀ ⥤ A₂)
    (p' : B₀ ⥤ B₁) (q' : B₁ ⥤ B₂) (r' : B₀ ⥤ B₂)
    (s : A₀ ⥤ B₀) (t : A₁ ⥤ B₁) (u : A₂ ⥤ B₂)
    (c : r ⟶ p ⋙ q) (c' : r' ⟶ p' ⋙ q')
    (a : p ⋙ t ⟶ s ⋙ p') (b : q ⋙ u ⟶ t ⋙ q') (z : r ⋙ u ⟶ s ⋙ r')
    {X : A₀} {Y : A₁} {Z Zc : A₂} {S : B₀} {T U : B₁}
    {V Vc H Hc Ht : B₂}
    (ek : p.obj X ⟶ Y) (eh : q.obj Y ⟶ Z) (er : r.obj X ⟶ Zc)
    (ev : s.obj X ⟶ S) (ew : t.obj Y ⟶ T)
    (ez : u.obj Z ⟶ V) (ezc : u.obj Zc ⟶ Vc)
    (fk : p'.obj S ⟶ U) (fh : q'.obj U ⟶ H)
    (fr : r'.obj S ⟶ Hc) (fht : q'.obj T ⟶ Ht)
    (dc : Zc ⟶ Z) (dl : Hc ⟶ H)
    (ak : T ⟶ U) (ah : V ⟶ Ht) (ar : Vc ⟶ Hc)
    (dz : Vc ⟶ V) (ak' : Ht ⟶ H)
    (nc : c.app X ≫ q.map ek ≫ eh = er ≫ dc)
    (nc' : c'.app S ≫ q'.map fk ≫ fh = fr ≫ dl)
    (nk : t.map ek ≫ ew ≫ ak = a.app X ≫ p'.map ev ≫ fk)
    (nh : u.map eh ≫ ez ≫ ah = b.app Y ≫ q'.map ew ≫ fht)
    (nr : u.map er ≫ ezc ≫ ar = z.app X ≫ r'.map ev ≫ fr)
    (nf : q'.map ak ≫ fh = fht ≫ ak')
    (ne : u.map dc ≫ ez = ezc ≫ dz)
    (ho : dz ≫ ah ≫ ak' = ar ≫ dl)
    [IsIso ev] [IsIso fk] [IsIso fh] :
    u.map (c.app X) ≫ b.app (p.obj X) ≫ q'.map (a.app X) =
      z.app X ≫ c'.app (s.obj X) := by
  let e := q'.map (p'.map ev) ≫ q'.map fk ≫ fh
  have : IsIso e := by dsimp only [e]; infer_instance
  apply (cancel_mono e).mp
  have hl :
      (u.map (c.app X) ≫ b.app (p.obj X) ≫ q'.map (a.app X)) ≫ e =
        u.map er ≫ ezc ≫ dz ≫ ah ≫ ak' := by
    dsimp only [e]
    have hnk := congrArg (fun f ↦ q'.map f) nk
    simp only [CategoryTheory.Functor.map_comp] at hnk
    simp only [Category.assoc]
    rw [← reassoc_of% hnk]
    rw [← reassoc_of% b.naturality ek, nf, ← reassoc_of% nh]
    have hnc := congrArg (fun f ↦ u.map f) nc
    simp only [CategoryTheory.Functor.map_comp] at hnc
    rw [reassoc_of% hnc, reassoc_of% ne]
  have hr : (z.app X ≫ c'.app (s.obj X)) ≫ e =
      u.map er ≫ ezc ≫ ar ≫ dl := by
    dsimp only [e]
    simp only [Category.assoc]
    rw [← reassoc_of% c'.naturality ev, nc', ← reassoc_of% nr]
  rw [hl, hr, ho]

private theorem primeStalkUnit (l : ℕ) (X : Scheme.{t})
    [∀ x : X, Invertible (l : X.residueField x)] (x : X) :
    IsUnit (l : X.presheaf.stalk x) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change (X.residue x).hom (l : X.presheaf.stalk x) ≠ 0
  simpa only [map_natCast] using (isUnit_of_invertible (l : X.residueField x)).ne_zero

/-- Source: Stacks Project, sites-cohomology.tex, Tag 0D6D.
(blueprint: lem-trf-sequence-derived-mixed-square).
Proof: Choose one flat-term K-flat resolution of the entire input quotient system. Exact geometric
inverse image preserves such complexes, and scalar extension preserves them for arbitrary
coefficient homomorphisms. The defining cochain counits for each geometric and scalar comparison
are invertible on this model. Compose their defining normalization equations along the two sides
of the square. Naturality moves counits across each whiskering, reducing both sides to the
ordinary scalar-generator interchange equation. Cancel the common target counit, then use
naturality and cancellation of the localized resolution isomorphism to obtain equality on every
derived object. All constructions are on the whole sequence site, so no evaluation or limit is
used. -/
theorem sequenceDerivedMixed
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {V W Z : Scheme.{t}}
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ x : W, Invertible (l : W.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)] (h : Z ⟶ W) (k : W ⟶ V) :
    Functor.whiskerRight (integralComparisonSystemComposition l E h k).hom
        (integralComparisonDerivedSequenceScalar l E L ι Z) ≫
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E k)
        (integralComparisonSystemScalarPullback l E L ι h).hom ≫
      Functor.whiskerRight (integralComparisonSystemScalarPullback l E L ι k).hom
        (integralComparisonDerivedSequencePullback l L h) =
    (integralComparisonSystemScalarPullback l E L ι (h ≫ k)).hom ≫
      Functor.whiskerLeft (integralComparisonDerivedSequenceScalar l E L ι V)
        (integralComparisonSystemComposition l L h k).hom  := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E V) K
  have := hf
  have : IsIso (DerivedCategory.Q.map f) := inferInstance
  apply (cancel_epi
    ((integralComparisonDerivedSequencePullback l E (h ≫ k) ⋙
      integralComparisonDerivedSequenceScalar l E L ι Z).map (DerivedCategory.Q.map f))).mp
  rw [NatTrans.naturality, NatTrans.naturality]
  suffices hp :
      (Functor.whiskerRight (integralComparisonSystemComposition l E h k).hom
          (integralComparisonDerivedSequenceScalar l E L ι Z) ≫
        Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E k)
          (integralComparisonSystemScalarPullback l E L ι h).hom ≫
        Functor.whiskerRight (integralComparisonSystemScalarPullback l E L ι k).hom
          (integralComparisonDerivedSequencePullback l L h)).app (DerivedCategory.Q.obj P) =
      ((integralComparisonSystemScalarPullback l E L ι (h ≫ k)).hom ≫
        Functor.whiskerLeft (integralComparisonDerivedSequenceScalar l E L ι V)
          (integralComparisonSystemComposition l L h k).hom).app (DerivedCategory.Q.obj P) by
    rw [hp]
  let p := integralComparisonSequencePullback l E k
  let q := integralComparisonSequencePullback l E h
  let r := integralComparisonSequencePullback l E (h ≫ k)
  let p' := integralComparisonSequencePullback l L k
  let q' := integralComparisonSequencePullback l L h
  let r' := integralComparisonSequencePullback l L (h ≫ k)
  let mV := integralComparisonSequenceScalarModel l E L ι V
  let mW := integralComparisonSequenceScalarModel l E L ι W
  let mZ := integralComparisonSequenceScalarModel l E L ι Z
  let c : r.mapDerivedCategory ≅ p.mapDerivedCategory ⋙ q.mapDerivedCategory :=
    integralComparisonSystemComposition l E h k
  let c' : r'.mapDerivedCategory ≅ p'.mapDerivedCategory ⋙ q'.mapDerivedCategory :=
    integralComparisonSystemComposition l L h k
  let sk : p.mapDerivedCategory ⋙ mW.T ≅ mV.T ⋙ p'.mapDerivedCategory :=
    integralComparisonSystemScalarPullback l E L ι k
  let sh : q.mapDerivedCategory ⋙ mZ.T ≅ mW.T ⋙ q'.mapDerivedCategory :=
    integralComparisonSystemScalarPullback l E L ι h
  let sr : r.mapDerivedCategory ⋙ mZ.T ≅ mV.T ⋙ r'.mapDerivedCategory :=
    integralComparisonSystemScalarPullback l E L ι (h ≫ k)
  let pc := p.mapHomologicalComplex (.up ℤ)
  let qc := q.mapHomologicalComplex (.up ℤ)
  let rc := r.mapHomologicalComplex (.up ℤ)
  let pc' := p'.mapHomologicalComplex (.up ℤ)
  let qc' := q'.mapHomologicalComplex (.up ℤ)
  let sv := mV.E.mapHomologicalComplex (.up ℤ)
  let sw := mW.E.mapHomologicalComplex (.up ℤ)
  let sz := mZ.E.mapHomologicalComplex (.up ℤ)
  let d : rc ⟶ pc ⋙ qc := (NatIso.mapHomologicalComplex
    (integralComparisonSequenceComposition l E h k) (.up ℤ)).hom
  let d' : (r'.mapHomologicalComplex (.up ℤ)) ⟶ pc' ⋙ qc' :=
    (NatIso.mapHomologicalComplex
    (integralComparisonSequenceComposition l L h k) (.up ℤ)).hom
  let ak : pc ⋙ sw ⟶ sv ⋙ pc' := (NatIso.mapHomologicalComplex
    (integralComparisonSequenceScalarPullback l E L ι k) (.up ℤ)).hom
  let ah : qc ⋙ sz ⟶ sw ⋙ qc' := (NatIso.mapHomologicalComplex
    (integralComparisonSequenceScalarPullback l E L ι h) (.up ℤ)).hom
  let ar : rc ⋙ sz ⟶ sv ⋙ r'.mapHomologicalComplex (.up ℤ) :=
    (NatIso.mapHomologicalComplex
    (integralComparisonSequenceScalarPullback l E L ι (h ≫ k)) (.up ℤ)).hom
  have hpk : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) (pc.obj P) := by
    apply sequencePullback_kflatgood l E k P hP
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (coefficientSequenceCommRingSheaf l E V) (P.X n)).symm (hflat n)
  have nk :=
    (integralComparisonSystemScalarPullback_existsUnique l E L ι k).exists.choose_spec P hP
  have nh :=
    (integralComparisonSystemScalarPullback_existsUnique l E L ι h).exists.choose_spec
      (pc.obj P) hpk
  have nr :=
    (integralComparisonSystemScalarPullback_existsUnique l E L ι (h ≫ k)).exists.choose_spec P hP
  have nc := exactComposition_fac p q r
    (integralComparisonSequenceComposition l E h k) P
  have nc' := exactComposition_fac p' q' r'
    (integralComparisonSequenceComposition l L h k) (sv.obj P)
  have ordinary := sequenceScalarGeometric_interchange_cochain l E L ι h k
    (primeStalkUnit l V) (primeStalkUnit l W) (primeStalkUnit l Z) P
  change mW.T.map (p.mapDerivedCategoryFactors.hom.app P) ≫
      mW.ε.app (pc.obj P) ≫ DerivedCategory.Q.map (ak.app P) =
    sk.hom.app (DerivedCategory.Q.obj P) ≫ p'.mapDerivedCategory.map (mV.ε.app P) ≫
      p'.mapDerivedCategoryFactors.hom.app (sv.obj P) at nk
  change mZ.T.map (q.mapDerivedCategoryFactors.hom.app (pc.obj P)) ≫
      mZ.ε.app (qc.obj (pc.obj P)) ≫ DerivedCategory.Q.map (ah.app (pc.obj P)) =
    sh.hom.app (DerivedCategory.Q.obj (pc.obj P)) ≫
      q'.mapDerivedCategory.map (mW.ε.app (pc.obj P)) ≫
      q'.mapDerivedCategoryFactors.hom.app (sw.obj (pc.obj P)) at nh
  change mZ.T.map (r.mapDerivedCategoryFactors.hom.app P) ≫
      mZ.ε.app (rc.obj P) ≫ DerivedCategory.Q.map (ar.app P) =
    sr.hom.app (DerivedCategory.Q.obj P) ≫ r'.mapDerivedCategory.map (mV.ε.app P) ≫
      r'.mapDerivedCategoryFactors.hom.app (sv.obj P) at nr
  change c.hom.app (DerivedCategory.Q.obj P) ≫
      q.mapDerivedCategory.map (p.mapDerivedCategoryFactors.hom.app P) ≫
      q.mapDerivedCategoryFactors.hom.app (pc.obj P) =
    r.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (d.app P) at nc
  change c'.hom.app (DerivedCategory.Q.obj (sv.obj P)) ≫
      q'.mapDerivedCategory.map (p'.mapDerivedCategoryFactors.hom.app (sv.obj P)) ≫
      q'.mapDerivedCategoryFactors.hom.app (pc'.obj (sv.obj P)) =
    r'.mapDerivedCategoryFactors.hom.app (sv.obj P) ≫
      DerivedCategory.Q.map (d'.app (sv.obj P)) at nc'
  have ho : sz.map (d.app P) ≫ ah.app (pc.obj P) ≫ qc'.map (ak.app P) =
      ar.app P ≫ d'.app (sv.obj P) := by
    apply HomologicalComplex.Hom.ext
    funext n
    have hn := congrArg (fun f ↦ f.f n) ordinary
    dsimp only [d, d', ak, ah, ar, sz, qc', pc, sv, p, q', mV, mZ]
    simpa only [sequenceScalarGeometricLeft, sequenceScalarGeometricRight,
      NatIso.mapHomologicalComplex, Functor.mapHomologicalComplex_obj_X,
      NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using hn
  have := mV.computes P hP
  change mZ.T.map (c.hom.app (DerivedCategory.Q.obj P)) ≫
      sh.hom.app (p.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
      q'.mapDerivedCategory.map (sk.hom.app (DerivedCategory.Q.obj P)) =
    sr.hom.app (DerivedCategory.Q.obj P) ≫
      c'.hom.app (mV.T.obj (DerivedCategory.Q.obj P))
  apply mixedPasting
    p.mapDerivedCategory q.mapDerivedCategory r.mapDerivedCategory
    p'.mapDerivedCategory q'.mapDerivedCategory r'.mapDerivedCategory
    mV.T mW.T mZ.T c.hom c'.hom sk.hom sh.hom sr.hom
    (p.mapDerivedCategoryFactors.hom.app P)
    (q.mapDerivedCategoryFactors.hom.app (pc.obj P))
    (r.mapDerivedCategoryFactors.hom.app P)
    (mV.ε.app P) (mW.ε.app (pc.obj P))
    (mZ.ε.app (qc.obj (pc.obj P))) (mZ.ε.app (rc.obj P))
    (p'.mapDerivedCategoryFactors.hom.app (sv.obj P))
    (q'.mapDerivedCategoryFactors.hom.app (pc'.obj (sv.obj P)))
    (r'.mapDerivedCategoryFactors.hom.app (sv.obj P))
    (q'.mapDerivedCategoryFactors.hom.app (sw.obj (pc.obj P)))
    (DerivedCategory.Q.map (d.app P)) (DerivedCategory.Q.map (d'.app (sv.obj P)))
    (DerivedCategory.Q.map (ak.app P)) (DerivedCategory.Q.map (ah.app (pc.obj P)))
    (DerivedCategory.Q.map (ar.app P))
    (DerivedCategory.Q.map (sz.map (d.app P)))
    (DerivedCategory.Q.map (qc'.map (ak.app P))) nc nc' nk nh nr
  · exact q'.mapDerivedCategoryFactors.hom.naturality (ak.app P)
  · exact mZ.ε.naturality (d.app P)
  · simpa only [CategoryTheory.Functor.map_comp] using
      congrArg (fun f ↦ DerivedCategory.Q.map f) ho

end WeilConjectures
