/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleSignedTensorPullbackTotal

/-! # Signed exchange on flat K-flat representatives

Source: Stacks 07A4, lemma-pullback-tensor-product, with the symmetry paragraph
after definition-derived-tor (06YU) and the signs of 0FNG.
(blueprint: lem-pur-finite-pullback-tensor-signed-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local implicit_reducible] pullbackTensorSwap
attribute [local implicit_reducible] coefficientTotalTensor Functor.map₂HomologicalComplex
  CoefficientTensorModels.iso coefficientFiniteInternalHom finiteIntrinsicDerivedTensor
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction pullbackTensorBraiding
  proEtaleTensorPullbackTotal proEtaleTensorPullbackTotalIso proEtaleRingDerivedPullbackFactors
  pullbackTensorSignedTotal HomologicalComplex₂.total
  CategoryTheory.Functor.mapBifunctorHomologicalComplex
private theorem normalizedSignedSquare
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : D × D ⥤ D)
    (β : T ≅ pullbackTensorSwap D ⋙ T)
    {M N U V : C} {A B M' N' U' V' : D}
    (b : U ⟶ V) (c : U' ⟶ V')
    (r : U ≅ M) (s : V ≅ N)
    (r' : U' ≅ T.obj (M', N')) (s' : V' ≅ T.obj (N', M'))
    (e : F.obj U ≅ U') (e' : F.obj V ≅ V')
    (j : M ⟶ N) (a : F.obj M ⟶ T.obj (A, B))
    (a' : F.obj N ⟶ T.obj (B, A))
    (x : A ≅ M') (y : B ≅ N')
    (h : b ≫ s.hom = r.hom ≫ j)
    (h' : c ≫ s'.hom = r'.hom ≫ β.hom.app (M', N'))
    (hn : F.map b ≫ e'.hom = e.hom ≫ c)
    (hr : F.map r.hom ≫ a ≫ T.map (Prod.mkHom x.hom y.hom) = e.hom ≫ r'.hom)
    (hs : F.map s.hom ≫ a' ≫ T.map (Prod.mkHom y.hom x.hom) = e'.hom ≫ s'.hom) :
    F.map j ≫ a' = a ≫ β.hom.app (A, B) := by
  apply (cancel_epi (F.mapIso r).hom).1
  apply (cancel_mono (T.mapIso (Iso.prod y x)).hom).1
  simp only [Functor.mapIso_hom, Iso.prod_hom, Category.assoc]
  calc
    _ = F.map b ≫ (F.map s.hom ≫ a' ≫ T.map (Prod.mkHom y.hom x.hom)) := by
      rw [← F.map_comp_assoc, ← h, F.map_comp_assoc]
    _ = e.hom ≫ c ≫ s'.hom := by rw [hs, ← Category.assoc, hn, Category.assoc]
    _ = (F.map r.hom ≫ a ≫ T.map (Prod.mkHom x.hom y.hom)) ≫
        β.hom.app (M', N') := by rw [h', hr]; simp only [Category.assoc]
    _ = _ := by
      have hβ := β.hom.naturality (Prod.mkHom x.hom y.hom)
      dsimp only [Functor.comp_map, pullbackTensorSwap] at hβ
      simp only [Category.assoc]
      rw [hβ]

private theorem signedSquare_transport
    {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (r : F ≅ G) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (β : T ≅ pullbackTensorSwap C ⋙ T) (γ : U ≅ pullbackTensorSwap D ⋙ U)
    (a : ∀ M N, F.obj (T.obj (M, N)) ⟶ U.obj (F.obj M, F.obj N))
    (M N : C)
    (h : F.map (β.hom.app (M, N)) ≫ a N M =
      a M N ≫ γ.hom.app (F.obj M, F.obj N)) :
    G.map (β.hom.app (M, N)) ≫
        (r.inv.app (T.obj (N, M)) ≫ a N M ≫ U.map (Prod.mkHom (r.hom.app N) (r.hom.app M))) =
      (r.inv.app (T.obj (M, N)) ≫ a M N ≫ U.map (Prod.mkHom (r.hom.app M) (r.hom.app N))) ≫
        γ.hom.app (G.obj M, G.obj N) := by
  calc
    _ = r.inv.app (T.obj (M, N)) ≫ (F.map (β.hom.app (M, N)) ≫ a N M) ≫
        U.map (Prod.mkHom (r.hom.app N) (r.hom.app M)) := by
      have hn : G.map (β.hom.app (M, N)) ≫ r.inv.app (T.obj (N, M)) =
          r.inv.app (T.obj (M, N)) ≫ F.map (β.hom.app (M, N)) :=
        r.inv.naturality (β.hom.app (M, N))
      rw [← Category.assoc, hn]
      simp only [Category.assoc]
    _ = _ := by
      rw [h]
      simp only [Category.assoc]
      have hγ := γ.hom.naturality (Prod.mkHom (r.hom.app M) (r.hom.app N))
      dsimp only [Functor.comp_map, pullbackTensorSwap] at hγ
      rw [hγ]

private def tensorModelRestriction (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (S : CoefficientClosedStructure
      (CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology W) R))
    (T : CoefficientTensorModels.{u, u + 1, u} (ProEt.topology W) R S) :
    ProEtaleTensorModel W R := by
  let i := ObjectProperty.ιOfLE
    (P := proEtaleFlatRepresentatives W R)
    (P' := CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology W) (R := R))
    (fun P hP ↦ pullbackTensorIndependent W R ⟨P, hP⟩)
  exact { tensor := S.tensor
          representative := Functor.isoWhiskerLeft (i.prod i) T.comparison }

attribute [local implicit_reducible] tensorModelRestriction

private theorem tensorModelRestriction_eq (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (S : CoefficientClosedStructure
      (CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology W) R))
    (T : CoefficientTensorModels.{u, u + 1, u} (ProEt.topology W) R S) :
    (pullbackTensorFiniteRepresentative_existsUnique W R S T).exists.choose =
      tensorModelRestriction W R S T := by
  apply (pullbackTensorFiniteRepresentative_existsUnique W R S T).unique
    (pullbackTensorFiniteRepresentative_existsUnique W R S T).exists.choose_spec
  exact ⟨rfl, fun _ _ ↦ HEq.rfl⟩

private theorem restrictedModelNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (SY : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology Y) R))
    (TY : CoefficientTensorModels.{u, u + 1, u} (ProEt.topology Y) R SY)
    (SX : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X) S))
    (TX : CoefficientTensorModels.{u, u + 1, u} (ProEt.topology X) S SX)
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (ha : a = tensorModelRestriction Y R SY TY)
    (hb : b = tensorModelRestriction X S SX TX)
    (ea : a.tensor = SY.tensor) (eb : b.tensor = SX.tensor)
    (M N : DerivedCategory (proEtaleRingModules Y R))
    {U V : DerivedCategory (proEtaleRingModules X S)}
    (pre : U ≅ (proEtaleRingDerivedPullback f R S c).obj (SY.tensor.obj (M, N)))
    (post : SX.tensor.obj ((proEtaleRingDerivedPullback f R S c).obj M,
      (proEtaleRingDerivedPullback f R S c).obj N) ≅ V) :
    (pre ≪≫ (proEtaleRingDerivedPullback f R S c).mapIso
        ((eqToIso ea).app (M, N)).symm ≪≫
      (proEtaleCanonicalTensorComparison f R S c a b).app (M, N) ≪≫
      (eqToIso eb).app ((proEtaleRingDerivedPullback f R S c).obj M,
        (proEtaleRingDerivedPullback f R S c).obj N) ≪≫ post).hom =
      pre.hom ≫ (proEtaleCanonicalTensorComparison f R S c
        (tensorModelRestriction Y R SY TY) (tensorModelRestriction X S SX TX)).hom.app
          (M, N) ≫ post.hom := by
  subst a
  subst b
  change SY.tensor = SY.tensor at ea
  change SX.tensor = SX.tensor at eb
  cases ea
  cases eb
  simp only [eqToIso_refl, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

private theorem canonicalSignedRepresentatives {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (SY : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology Y) R))
    (TY : CoefficientTensorModels.{u, u + 1, u} (ProEt.topology Y) R SY)
    (SX : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X) S))
    (TX : CoefficientTensorModels.{u, u + 1, u} (ProEt.topology X) S SX)
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hP : proEtaleFlatRepresentatives Y R P)
    (hQ : proEtaleFlatRepresentatives Y R Q) :
    let F := proEtaleRingDerivedPullback f R S c
    let α := proEtaleCanonicalTensorComparison f R S c
      (tensorModelRestriction Y R SY TY) (tensorModelRestriction X S SX TX)
    F.map ((pullbackTensorBraiding (ProEt.topology Y) R SY TY).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        α.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
      α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (pullbackTensorBraiding (ProEt.topology X) S SX TX).hom.app
          (F.obj (DerivedCategory.Q.obj P), F.obj (DerivedCategory.Q.obj Q)) := by
  let F := proEtaleRingDerivedPullback f R S c
  let L := (proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)
  let a := tensorModelRestriction Y R SY TY
  let b := tensorModelRestriction X S SX TX
  let α := proEtaleCanonicalTensorComparison f R S c a b
  let δ := proEtaleRingDerivedPullbackFactors f R S c
  let βY := pullbackTensorBraiding (ProEt.topology Y) R SY TY
  let βX := pullbackTensorBraiding (ProEt.topology X) S SX TX
  let t := CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor Y R)
  let t' := CochainComplex.mapBifunctor Q P (proEtaleOrdinaryTensor Y R)
  let u := CochainComplex.mapBifunctor (L.obj P) (L.obj Q) (proEtaleOrdinaryTensor X S)
  let u' := CochainComplex.mapBifunctor (L.obj Q) (L.obj P) (proEtaleOrdinaryTensor X S)
  let σY : t ≅ t' := pullbackTensorSignedTotal (ProEt.topology Y) R P Q
  let σX : u ≅ u' := pullbackTensorSignedTotal (ProEt.topology X) S (L.obj P) (L.obj Q)
  let κ := proEtaleTensorPullbackTotalIso f R S c P Q
  let κ' := proEtaleTensorPullbackTotalIso f R S c Q P
  have hP' := (proEtaleCanonicalTensorPullback f R S c a b).1 P hP
  have hQ' := (proEtaleCanonicalTensorPullback f R S c a b).1 Q hQ
  let r := a.representative.app (⟨P, hP⟩, ⟨Q, hQ⟩)
  let s := a.representative.app (⟨Q, hQ⟩, ⟨P, hP⟩)
  let r' := b.representative.app (⟨L.obj P, hP'⟩, ⟨L.obj Q, hQ'⟩)
  let s' := b.representative.app (⟨L.obj Q, hQ'⟩, ⟨L.obj P, hP'⟩)
  let e := δ.app t ≪≫ (DerivedCategory.Q.mapIso κ).symm
  let e' := δ.app t' ≪≫ (DerivedCategory.Q.mapIso κ').symm
  have hσY : DerivedCategory.Q.map σY.hom ≫ s.hom =
      r.hom ≫ βY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
    change DerivedCategory.Q.map σY.hom ≫
        (TY.comparison.app (⟨Q, hQ.1⟩, ⟨P, hP.1⟩)).hom =
      (TY.comparison.app (⟨P, hP.1⟩, ⟨Q, hQ.1⟩)).hom ≫
        βY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
    unfold σY βY pullbackTensorBraiding
    exact (pullbackTensorBraiding_existsUnique (ProEt.topology Y) R SY TY).exists.choose_spec
      P Q hP.1 hQ.1
  have hσX : DerivedCategory.Q.map σX.hom ≫ s'.hom =
      r'.hom ≫ βX.hom.app (DerivedCategory.Q.obj (L.obj P),
        DerivedCategory.Q.obj (L.obj Q)) := by
    change DerivedCategory.Q.map σX.hom ≫
        (TX.comparison.app (⟨L.obj Q, hQ'.1⟩, ⟨L.obj P, hP'.1⟩)).hom =
      (TX.comparison.app (⟨L.obj P, hP'.1⟩, ⟨L.obj Q, hQ'.1⟩)).hom ≫
        βX.hom.app (DerivedCategory.Q.obj (L.obj P), DerivedCategory.Q.obj (L.obj Q))
    unfold σX βX pullbackTensorBraiding
    exact (pullbackTensorBraiding_existsUnique (ProEt.topology X) S SX TX).exists.choose_spec
      (L.obj P) (L.obj Q) hP'.1 hQ'.1
  have hn : F.map (DerivedCategory.Q.map σY.hom) ≫ e'.hom =
      e.hom ≫ DerivedCategory.Q.map σX.hom := by
    change F.map (DerivedCategory.Q.map σY.hom) ≫ δ.hom.app t' ≫
        DerivedCategory.Q.map κ'.inv =
      (δ.hom.app t ≫ DerivedCategory.Q.map κ.inv) ≫ DerivedCategory.Q.map σX.hom
    have hδ := δ.hom.naturality σY.hom
    dsimp only [Functor.comp_map] at hδ
    simp only [Category.assoc]
    rw [← Category.assoc, hδ]
    simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
    rw [proEtaleSignedTensorPullbackTotal f R S c P Q]
  have hr : F.map r.hom ≫ α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      b.tensor.map (Prod.mkHom (δ.hom.app P) (δ.hom.app Q)) = e.hom ≫ r'.hom := by
    obtain ⟨hp, hq, h⟩ := (proEtaleCanonicalTensorPullback f R S c a b).2.exists.choose_spec
      P Q hP hQ
    dsimp only [e, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_inv]
    erw [Category.assoc]
    exact h
  have hs : F.map s.hom ≫ α.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
      b.tensor.map (Prod.mkHom (δ.hom.app Q) (δ.hom.app P)) = e'.hom ≫ s'.hom := by
    obtain ⟨hq, hp, h⟩ := (proEtaleCanonicalTensorPullback f R S c a b).2.exists.choose_spec
      Q P hQ hP
    dsimp only [e', Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_inv]
    erw [Category.assoc]
    exact h
  exact normalizedSignedSquare F b.tensor βX
    (DerivedCategory.Q.map σY.hom) (DerivedCategory.Q.map σX.hom)
    r s r' s' e e' (βY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (α.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
    (δ.app P) (δ.app Q) hσY hσX hn hr hs

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical comparison preserves signed exchange on flat K-flat inputs.
Source: Stacks Project, Cohomology on Sites, Tag 07A4, final displayed total map;
Tag 06YS for K-flat resolutions; Tag 06YU and its following symmetry paragraph;
More on Algebra, Tag 0FNG, section-sign-rules, item-flip-tensor-product.
(blueprint: lem-pur-finite-pullback-tensor-signed-representatives).
Proof: pullback preserves the flat K-flat representative class by
proEtaleCanonicalTensorPullback. Use its normalization square for (P,Q) and (Q,P).
The two signed braidings are fixed on these representatives by
pullbackTensorBraiding_existsUnique. In total degree k, restrict the ordinary
pullback comparison to the summand P^p tensor Q^q with p+q=k. Its defining
ordinary tensor map sends the pullback of x tensor y to f*x tensor f*y.
Exchanging before or after this map sends that generator to
(-1)^(p*q) f*y tensor f*x. The ordinary map is linear, so it commutes with this
sign, including negative degrees. The tensor generators, module sheafification
and total coproduct injections determine the chain maps. Thus the signed
chain square commutes. Apply the derived quotient and insert the two
representative normalization squares. Finally conjugate with the recorded
tensor-model isomorphisms and the unit-normalized realization. Naturality
cancels those conjugations and gives the displayed square. This only proves
coherence on the displayed flat K-flat complexes; extension to arbitrary
derived objects is a separate naturality argument. -/
theorem finitePullbackTensor_signed_representatives {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) P)
    (hQ : proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y n) Q) :
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    (finiteDerivedPullback l E n f).map
      ((pullbackTensorBraiding (ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)
        (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)).hom.app (M,N)) ≫
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) N M).hom =
    ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M N).hom ≫
      (pullbackTensorBraiding (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
        (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)).hom.app
          ((finiteDerivedPullback l E n f).obj M,(finiteDerivedPullback l E n f).obj N) := by
  let R := integralCoefficientCommRingSheaf l E Y n
  let S := integralCoefficientCommRingSheaf l E X n
  let c := pullbackTensorCoefficientIso l E f n
  let F := proEtaleRingDerivedPullback f R S c
  let G := finiteDerivedPullback l E n f
  let r : F ≅ G :=
    @Functor.mapDerivedCategoryNatIso
      (normalizedDVRModules l E Y n) (normalizedDVRModules l E X n) _ _
      (SheafOfModules.instAbelian (integralCoefficientSheaf l E Y n))
      (SheafOfModules.instAbelian (integralCoefficientSheaf l E X n)) _ _
      (proEtaleRingModulePullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
      (proEtaleRingModulePullback_additive f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f)
      (proEtaleRingModulePullback_preservesFiniteLimits f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (proEtaleRingModulePullback_preservesFiniteColimits f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f)
      (sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f)
      (pullbackTensorFiniteRealization l E f n)
  let a := tensorModelRestriction Y R (finiteIntrinsicClosed l E Y n)
    (finiteIntrinsicTensorModels l E Y n)
  let b := tensorModelRestriction X S (finiteIntrinsicClosed l E X n)
    (finiteIntrinsicTensorModels l E X n)
  let α := proEtaleCanonicalTensorComparison f R S c a b
  let βY := pullbackTensorBraiding (ProEt.topology Y) R
    (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)
  let βX := pullbackTensorBraiding (ProEt.topology X) S
    (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)
  have h := canonicalSignedRepresentatives f R S c
    (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)
    (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) P Q hP hQ
  have ht := signedSquare_transport F G r
    (finiteIntrinsicDerivedTensor l E Y n) (finiteIntrinsicDerivedTensor l E X n)
    βY βX (fun M N ↦ α.hom.app (M, N))
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) h
  have hμ (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M N).hom =
        r.inv.app ((finiteIntrinsicDerivedTensor l E Y n).obj (M, N)) ≫
          α.hom.app (M, N) ≫ (finiteIntrinsicDerivedTensor l E X n).map
            (Prod.mkHom (r.hom.app M) (r.hom.app N)) := by
    unfold finitePullbackTensorConstruction
    exact restrictedModelNormalization f R S c
      (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)
      (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)
      (pullbackTensorFiniteModel l E Y n) (pullbackTensorFiniteModel l E X n)
      (tensorModelRestriction_eq Y R _ _) (tensorModelRestriction_eq X S _ _)
      (pullbackTensorFiniteRepresentative_existsUnique Y R _ _).exists.choose_spec.1
      (pullbackTensorFiniteRepresentative_existsUnique X S _ _).exists.choose_spec.1 M N
      (r.app ((finiteIntrinsicDerivedTensor l E Y n).obj (M, N))).symm
      ((finiteIntrinsicDerivedTensor l E X n).mapIso
        (Iso.prod (r.app M) (r.app N)))
  dsimp only
  exact (congrArg (fun v ↦ G.map (βY.hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫ v)
    (hμ (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P))).trans
      (ht.trans (congrArg (fun v ↦ v ≫ βX.hom.app
        (G.obj (DerivedCategory.Q.obj P), G.obj (DerivedCategory.Q.obj Q)))
        (hμ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).symm))
end WeilConjectures
