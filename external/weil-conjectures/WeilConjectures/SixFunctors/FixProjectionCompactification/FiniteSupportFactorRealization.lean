/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionCompactificationData
import WeilConjectures.SixFunctors.FixProjectionCompactification.FiniteSupportIdentityFactorCompositor
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteRealizationEtaleOrigin

/-! # Finite realization of the canonical proper/open support identification

Source: def-sf-operation-stages, normalized support composition and proper/open identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification

attribute [local implicit_reducible] sixFunctorFiniteSupport sixFunctorFiniteOpen
  sixFunctorFiniteRealization sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  sixFunctorFactorCompactification sixFunctorOpenCompactification
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  sfIntrinsicDerivedEquivalence sfIntrinsicCompactSupportComparison
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem cancel_witness
    {A B C : Type*} [Category A] [Category B] [Category C]
    (P O : A ⥤ B) (Q G : B ⥤ C) (e : P ≅ O) (d : Q ≅ G)
    {M K : A} (w : M ≅ K) {H U : B} {V W J T : C}
    (rho : H ≅ P.obj K) (sigma : J ≅ Q.obj H) (tau : T ≅ G.obj (O.obj K))
    (ei : P.obj M ≅ U) (ep : Q.obj U ≅ V) (ef : G.obj (O.obj M) ≅ W)
    (a : V ⟶ W) (alpha : J ⟶ T)
    (hnorm : alpha ≫ tau.hom ≫ G.map (O.map w.inv) ≫ ef.hom =
      sigma.hom ≫ Q.map (rho.hom ≫ P.map w.inv ≫ ei.hom) ≫ ep.hom ≫ a)
    (hgeom : Q.map ei.hom ≫ ep.hom ≫ a =
      d.hom.app (P.obj M) ≫ G.map (e.hom.app M) ≫ ef.hom) :
    alpha ≫ tau.hom =
      sigma.hom ≫ Q.map rho.hom ≫ d.hom.app (P.obj K) ≫ G.map (e.hom.app K) := by
  apply (cancel_mono (G.map (O.map w.inv))).mp
  apply (cancel_mono ef.hom).mp
  simp only [Category.assoc, Functor.map_comp] at hnorm ⊢
  rw [hnorm, hgeom]
  rw [reassoc_of% (d.hom.naturality (P.map w.inv))]
  rw [← G.map_comp_assoc, e.hom.naturality w.inv, G.map_comp]
  simp only [Category.assoc]

private theorem support_composition_factor
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (F : SixFunctorFiniteOperations D C E n hn)
    {X Z Y : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
    (hi : IsOpenImmersion i.hom.left) (hp : IsProper p.hom.left)
    [QuasiCompact i.hom.left] (K : sixFunctorFiniteCategory D C E n hn X) :
    letI := hp
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := Padic.coefficientExtensionRing C.l E n
    let ci := sixFunctorOpenCompactification i hi
    let cp := Compactification.ofIsProper p.hom.left
    let c := sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
        ((F.finite.composition i p ci cp c).inv.app K) ≫
      (F.finiteSupport (i ≫ p) c).hom.app K =
    (F.finiteSupport p cp).hom.app ((F.finite.support i ci).obj K) ≫
      (sfIntrinsicCompactSupport cp A).map ((F.finiteSupport i ci).hom.app K) ≫
      (sixFunctorProperCandidateIso A p.hom.left).hom.app
        ((sfIntrinsicCompactSupport ci A).obj K.obj) ≫
      (proEtaleConstantDerivedDirectImage p.hom.left A).map
        ((@sixFunctorOpenCandidateIso A _ _ X.obj.left Z.obj.left i.hom.left hi).hom.app
          K.obj) := by
  let := hp
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := Padic.coefficientExtensionRing C.l E n
  let Λ := ULift.{u + 1} A
  let : TopologicalSpace Λ := ⊥
  let := discreteTopology_bot Λ
  let ci := sixFunctorOpenCompactification i hi
  let cp := Compactification.ofIsProper p.hom.left
  let c := sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl
  let RX := sixFunctorFiniteRealization D C E n hn X
  obtain ⟨L, hL, ⟨e⟩⟩ := CompactSupportFiniteProjection.finiteRealization_etaleOrigin X K
  let L₀ : DerivedCategory.Plus (Sheaf X.obj.left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) := ⟨L, hL⟩
  let O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left :=
    ⟨(finiteCoefficientComparison X.obj.left Λ).mapDerivedCategoryPlus.obj L₀,
      ⟨L₀, Iso.refl _⟩⟩
  let M := refinementFiniteLevelFixedObject C.l E n hn X.obj.left O
  let a := refinementFixedWitnessIso X.obj.left Λ O
  let w : RX.functor.obj M ≅ K.obj :=
    RX.functor.mapIso (a.symm ≪≫ e) ≪≫ RX.counitIso.app K.obj
  have hnorm := F.finiteCompositionNormalization i p ci cp c K O w
  have hgeom := finiteSupportIdentityFactorCompositor D C E n hn i p hi hp O
  apply cancel_witness
    (sfIntrinsicCompactSupport ci A)
    (@sfIntrinsicExtensionByZero X.obj.left Z.obj.left i.hom.left hi A _ _).mapDerivedCategory
    (sfIntrinsicCompactSupport cp A) (proEtaleConstantDerivedDirectImage p.hom.left A)
    (@sixFunctorOpenCandidateIso A _ _ X.obj.left Z.obj.left i.hom.left hi)
    (sixFunctorProperCandidateIso A p.hom.left) w
    ((F.finiteSupport i ci).app K)
    ((F.finiteSupport p cp).app ((F.finite.support i ci).obj K))
    ((F.finiteSupport (i ≫ p) c).app K)
    ((sfIntrinsicCompactSupportComparison A ci).app M)
    ((sfIntrinsicCompactSupportComparison A cp).app ((sfFixedCompactSupport A ci).obj M))
    ((sfIntrinsicCompactSupportComparison A c).app M)
    ((sixFunctorFiniteRealization D C E n hn Y).functor.map
      (sixFunctorFiniteCompositionComparison C E n hn i p ci cp c O))
    ((intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
      ((F.finite.composition i p ci cp c).inv.app K))
  · simpa only [sixFunctorFiniteWitnessSupport, sixFunctorFiniteCompositeWitnessSupport,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.map_comp, Category.assoc, sixFunctorFiniteSupport, sfIntrinsicCompactSupport,
      sfAmbientCompactSupportCandidate, sixFunctorFactorCompactification,
      Functor.comp_map, ObjectProperty.ι_obj, A, ci, cp, c, M] using hnorm
  · exact hgeom

private theorem cancel_factor
    {B C V W : Type*} [Category B] [Category C] [Category V] [Category W]
    (S P : B ⥤ C) (I : C ⥤ W) (J : B ⥤ V) (Q G : V ⥤ W)
    (k : S ≅ P) (rho : S ⋙ I ≅ J ⋙ Q) (delta : P ⋙ I ≅ J ⋙ G)
    (d : Q ≅ G) {L L' : B} {M N : V} {T : C}
    (o : L ≅ L') (r : J.obj L ≅ M) (s : J.obj L' ≅ N) (e : M ≅ N)
    (c : T ≅ S.obj L) (t : I.obj T ≅ G.obj N)
    (hp : I.map (k.hom.app L) ≫ delta.hom.app L =
      rho.hom.app L ≫ d.hom.app (J.obj L))
    (ho : J.map o.hom ≫ s.hom = r.hom ≫ e.hom)
    (hc : I.map c.inv ≫ t.hom =
      rho.hom.app L ≫ Q.map r.hom ≫ d.hom.app M ≫ G.map e.hom) :
    I.map (k.inv.app L' ≫ S.map o.inv ≫ c.inv) ≫ t.hom =
      delta.hom.app L' ≫ G.map s.hom := by
  have hd := d.hom.naturality r.hom
  have hn := delta.hom.naturality o.hom
  have hk := k.hom.naturality o.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, reassoc_of% hd, ← reassoc_of% hp]
  rw [← G.map_comp, ← ho, G.map_comp]
  rw [← reassoc_of% hn]
  have hm := congrArg I.map hk
  simp only [Functor.map_comp] at hm
  rw [← reassoc_of% hm]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
  rw [S.map_id, Category.id_comp, Iso.inv_hom_id_app, I.map_id, Category.id_comp]

private theorem factor_realization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (F : SixFunctorFiniteOperations D C E n hn)
    {X Z Y : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
    (hi : IsOpenImmersion i.hom.left) (hp : IsProper p.hom.left)
    [QuasiCompact i.hom.left] (f : X ⟶ Y) (h : f = i ≫ p)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
        ((sixFunctorFactoredSupportIdentification F.finite i p hi hp f h).inv.app K) ≫
      (F.finiteSupport f (sixFunctorFactorCompactification i p hi hp f h)).hom.app K =
    (F.finiteDirectImage p).hom.app ((F.finite.openExtension i hi).obj K) ≫
      (proEtaleConstantDerivedDirectImage p.hom.left
        (Padic.coefficientExtensionRing C.l E n)).map
          ((F.finiteOpenExtension i hi).hom.app K) := by
  subst f
  let := hp
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := Padic.coefficientExtensionRing C.l E n
  let IY := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
  let IZ := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
  let ci := sixFunctorOpenCompactification i hi
  let cp := Compactification.ofIsProper p.hom.left
  let c := sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl
  have hd := congrArg Iso.hom
    (F.finiteProperNormalization p ((F.finite.support i ci).obj K))
  have he := congrArg Iso.hom (F.finiteOpenNormalization i hi K)
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hd he
  have hb := support_composition_factor D C E n hn F i p hi hp K
  have hc := cancel_factor
    (F.finite.support p cp) (F.finite.direct p) IY IZ
    (sfIntrinsicCompactSupport cp A) (proEtaleConstantDerivedDirectImage p.hom.left A)
    (F.finite.properIdentity p) (F.finiteSupport p cp) (F.finiteDirectImage p)
    (sixFunctorProperCandidateIso A p.hom.left)
    ((F.finite.openIdentification i hi).app K)
    ((F.finiteSupport i ci).app K) ((F.finiteOpenExtension i hi).app K)
    ((@sixFunctorOpenCandidateIso A _ _ X.obj.left Z.obj.left i.hom.left hi).app K.obj)
    ((F.finite.composition i p ci cp c).app K) ((F.finiteSupport (i ≫ p) c).app K)
    hd he hb
  simpa only [sixFunctorFactoredSupportIdentification, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.app_inv, Iso.app_hom, Functor.map_comp, Category.assoc]
    using hc

/-- The finite support realization respects its actual proper/open factorization.
This is a single finite coefficient ring; no integral reduction or system realization
is present in the equation.

Source: def-sf-operation-stages, finiteCompositionNormalization,
finiteOpenNormalization and finiteProperNormalization; prop-sf-pf-coherence.proof.md,
compatibility of comparisons with counits and j_!.
(blueprint: lem-sf-finite-support-factor-realization).

Proof: expand sixFunctorFactoredSupportIdentification as composition followed by the
open identification and proper identification. Use a bounded etale-origin witness for
the finite constructible input in finiteCompositionNormalization. Its origin compositor
is the canonical open/proper composite for this same compactification. At the open and
proper compactifications, finiteOpenNormalization cancels the identity proper image and
finiteProperNormalization cancels the identity open extension. Naturality of the two
finite realization isomorphisms moves the input comparison through proper image. The
three retained origin-witness comparisons cancel, leaving finiteSupport on the source
and finiteDirectImage followed by direct image of finiteOpenExtension on the target.
The source compositor is inverted in the displayed equation, so the result is the
inverse factored support identification followed by finiteSupport. All equality
transports use Q.factorization and the very compactification Q.compactification;
there is no change of compactification. Zero inputs, identity factors and the empty
open use the corresponding identity/unit cancellations. -/
theorem finiteSupportFactorRealization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (F : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [QuasiCompact f.hom.left] (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    let Q := identitySquare f c
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
        ((sixFunctorFactoredSupportIdentification F.finite Q.i Q.p Q.open_i Q.proper_p
          Q.f Q.factorization).inv.app K) ≫
      (F.finiteSupport f c).hom.app K =
    (F.finiteDirectImage Q.p).hom.app ((F.finite.openExtension Q.i Q.open_i).obj K) ≫
      (proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing C.l E n)).map
          ((F.finiteOpenExtension Q.i Q.open_i).hom.app K) := by
  let Q := identitySquare f c
  let := X.property.1
  let := X.property.2
  let := LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  let := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  let : IsNoetherian X.obj.left := {}
  have : QuasiCompact Q.i.hom.left := by
    change QuasiCompact c.i
    infer_instance
  exact factor_realization D C E n hn F Q.i Q.p Q.open_i Q.proper_p Q.f
    Q.factorization K

end WeilConjectures.FixProjectionCompactification
