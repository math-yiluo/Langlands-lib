/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalReductionConeCalculus
public import WeilConjectures.SixFunctors.ProEtale.InternalQuotientTowerModel
import WeilConjectures.SixFunctors.ProEtale.InternalUniformizerKoszulScalarSquare
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone

/-! # Singleton Koszul coordinates after exact coefficient transport

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
the finite free dual calculation; blueprint proposition-direct-image-along-open-immersion--1,
Reduction paragraph. (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

-- The tip's universe-shrinking `hasLimitsOfSize_of_succ` loops (typeclass timeout on `Mono b.hom`).
attribute [-instance] CategoryTheory.Limits.hasLimitsOfSize_of_succ
attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap
attribute [local irreducible] ringedKoszulDualTower
attribute [local irreducible] ringedKoszulRightUnitIso ringedKoszulTensorUnitComponent

private def coneSquareIso {A : Type*} [Category A] [Preadditive A]
    [HasBinaryBiproducts A] {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : K ≅ K') (b : L ≅ L')
    (h : f ≫ b.hom = a.hom ≫ f') :
    CochainComplex.mappingCone f ≅ CochainComplex.mappingCone f' where
  hom := CochainComplex.mappingCone.map f f' a.hom b.hom h
  inv := CochainComplex.mappingCone.map f' f a.inv b.inv (by
    rw [← cancel_epi a.hom, ← cancel_mono b.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc, h])
  hom_inv_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simpa only [Iso.hom_inv_id] using CochainComplex.mappingCone.map_id f
  inv_hom_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simpa only [Iso.inv_hom_id] using CochainComplex.mappingCone.map_id f'

private theorem transport_cone_coordinates
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B]
    (F : A ⥤ B) [F.Additive] {P : CochainComplex A ℤ} {V D : CochainComplex B ℤ}
    (s : End P) (r : End V)
    (b : ((F.mapHomologicalComplex (.up ℤ)).obj P) ≅ V)
    (U : V ≅ (F.mapHomologicalComplex (.up ℤ)).obj P)
    (hb : (F.mapHomologicalComplex (.up ℤ)).map s.asHom ≫ U.inv = b.hom ≫ r.asHom)
    (k : CochainComplex.mappingCone r.asHom ≅ D)
    (η : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ D)
    (Z : ℤ → B) (ι : ∀ q, Z q ⟶ D.X q)
    (hk₀ : CochainComplex.mappingCone.inr r.asHom ≫ k.hom = U.hom ≫ η)
    (hk₁ : ∀ q : ℤ, ∃ z : F.obj (P.X (q + 1)) ⟶ Z q,
      U.inv.f (q + 1) ≫ (CochainComplex.mappingCone.inl r.asHom).v
        (q + 1) q (by omega) ≫ k.hom.f q = z ≫ ι q) :
    ∃ e : (F.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCone s.asHom) ≅ D,
      (∀ q : ℤ, F.map ((CochainComplex.mappingCone.inr s.asHom).f q) ≫ e.hom.f q = η.f q) ∧
      (∀ q : ℤ, ∃ z : F.obj (P.X (q + 1)) ⟶ Z q,
        F.map ((CochainComplex.mappingCone.inl s.asHom).v (q + 1) q (by omega)) ≫
          e.hom.f q = z ≫ ι q) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let m := CochainComplex.mappingCone.mapHomologicalComplexIso s.asHom F
  let c := coneSquareIso (G.map s.asHom) r.asHom b U.symm hb
  let e := m ≪≫ c ≪≫ k
  refine ⟨e, ?_, ?_⟩
  · intro q
    have hm := congrArg (fun t ↦ t.f q) (CochainComplex.mappingCone.map_inr s.asHom F)
    have hc : CochainComplex.mappingCone.inr (G.map s.asHom) ≫ c.hom =
        U.inv ≫ CochainComplex.mappingCone.inr r.asHom := by
      simp [c, coneSquareIso, CochainComplex.mappingCone.map]
    have hh := congrArg (fun t ↦ t.f q) hc
    have hk := congrArg (fun t ↦ t.f q) hk₀
    change F.map ((CochainComplex.mappingCone.inr s.asHom).f q) ≫
      (m.hom.f q ≫ c.hom.f q ≫ k.hom.f q) = _
    change F.map ((CochainComplex.mappingCone.inr s.asHom).f q) ≫ m.hom.f q =
      (CochainComplex.mappingCone.inr (G.map s.asHom)).f q at hm
    simp only [HomologicalComplex.comp_f] at hh hk
    rw [← Category.assoc, ← Category.assoc, hm, hh, Category.assoc, hk]
    change U.inv.f q ≫ U.hom.f q ≫ _ = _
    have hU : U.inv.f q ≫ U.hom.f q = 𝟙 _ :=
      congrArg (fun f ↦ f.f q) U.inv_hom_id
    rw [← Category.assoc, hU, Category.id_comp]
  · intro q
    obtain ⟨z, hz⟩ := hk₁ q
    refine ⟨b.hom.f (q + 1) ≫ U.hom.f (q + 1) ≫ z, ?_⟩
    have hm : F.map ((CochainComplex.mappingCone.inl s.asHom).v
          (q + 1) q (by omega)) ≫ m.hom.f q =
        (CochainComplex.mappingCone.inl (G.map s.asHom)).v (q + 1) q (by omega) := by
      change _ ≫ (CochainComplex.mappingCone.mapHomologicalComplexXIso' s.asHom F
        q (q + 1) rfl).hom = _
      simp only [CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
        Preadditive.comp_add, ← F.map_comp_assoc,
        CochainComplex.mappingCone.inl_v_fst_v, CochainComplex.mappingCone.inl_v_snd_v,
        F.map_id, F.map_zero, Category.id_comp, zero_comp, add_zero]
      rfl
    have hc : (CochainComplex.mappingCone.inl (G.map s.asHom)).v
          (q + 1) q (by omega) ≫ c.hom.f q =
        b.hom.f (q + 1) ≫ (CochainComplex.mappingCone.inl r.asHom).v
          (q + 1) q (by omega) := by
      simp [c, coneSquareIso, CochainComplex.mappingCone.map]
    change F.map ((CochainComplex.mappingCone.inl s.asHom).v (q + 1) q (by omega)) ≫
      (m.hom.f q ≫ c.hom.f q ≫ k.hom.f q) = _
    rw [← Category.assoc, ← Category.assoc, hm, hc]
    calc
      _ = (b.hom.f (q + 1) ≫ U.hom.f (q + 1)) ≫
          (U.inv.f (q + 1) ≫ (CochainComplex.mappingCone.inl r.asHom).v
            (q + 1) q (by omega) ≫ k.hom.f q) := by
        have hU : U.hom.f (q + 1) ≫ U.inv.f (q + 1) = 𝟙 _ :=
          congrArg (fun f ↦ f.f (q + 1)) U.hom_inv_id
        simp only [Category.assoc]
        rw [← Category.assoc (U.hom.f (q + 1)) (U.inv.f (q + 1)),
          hU, Category.id_comp]
      _ = _ := by rw [hz]; simp only [Category.assoc]

section Ringed
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})
local instance internalKoszulConeCoordinatesInst1 : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.isGrothendieckAbelian _
local instance internalKoszulConeCoordinatesInst2 : MonoidalCategory (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.monoidalCategory O
local instance internalKoszulConeCoordinatesInst3 : SymmetricCategory (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.symmetricCategory O
local instance internalKoszulConeCoordinatesInst4 : MonoidalPreadditive (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  Classical.choice (SheafOfModules.tensorClosed O).1
local instance internalKoszulConeCoordinatesInst5 : MonoidalClosed (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  Classical.choice (SheafOfModules.tensorClosed O).2.1
local instance internalKoszulConeCoordinatesInst6 (K L : ringedSiteComplex O) :
    HomologicalComplex.HasMapBifunctor K L (curriedTensor _) (.up ℤ) := inferInstance

private theorem coefficient_cone
    (a : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    ∃ e : CochainComplex.mappingCone
        ((HomologicalComplex.single _ (.up ℤ) 0).map
          (ringedKoszulScalar O a ^ (n + 1)).asHom) ≅
        (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n),
      CochainComplex.mappingCone.inr _ ≫ e.hom = ringedKoszulDualUnit O 1 (fun _ ↦ a) n := by
  let I := ringedSiteRingComplex O
  let Q := (ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n)
  let f : I ⟶ I := (HomologicalComplex.single _ (.up ℤ) 0).map
    (ringedKoszulScalar O a ^ (n + 1)).asHom
  let g := ringedSingletonKoszulPower O a I n
  let L : ((ringedKoszulTensor O).obj I).obj I ≅ I := HomologicalComplex.leftUnitor I
  let LQ : ((ringedKoszulTensor O).obj I).obj Q ≅ Q := HomologicalComplex.leftUnitor Q
  have h : g.asHom ≫ L.hom = L.hom ≫ f := by
    unfold g ringedSingletonKoszulPower
    exact leftUnitor_naturality f
  let sq := coneSquareIso g.asHom f L L h
  obtain ⟨e, he, _, _⟩ := ringedSingletonKoszulCone O a I
  let en : ((ringedKoszulTensor O).obj I).obj Q ≅
      CochainComplex.mappingCone g.asHom := e n
  have he₀ : ringedKoszulTensorUnitComponent O 1 (fun _ ↦ a) I (op n) ≫ en.hom =
      (ringedKoszulRightUnitIso O I).inv ≫ CochainComplex.mappingCone.inr g.asHom := he n
  let c := sq.symm ≪≫ en.symm ≪≫ LQ
  refine ⟨c, ?_⟩
  have hi : CochainComplex.mappingCone.inr g.asHom ≫ en.inv =
      ((ringedKoszulTensor O).obj I).map (ringedKoszulDualUnit O 1 (fun _ ↦ a) n) := by
    have hh := congrArg (fun t ↦ (ringedKoszulRightUnitIso O I).hom ≫ t ≫ en.inv)
      he₀
    simpa only [ringedKoszulTensorUnitComponent, Category.assoc,
      Iso.inv_hom_id, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using hh.symm
  have hs : CochainComplex.mappingCone.inr f ≫ sq.inv =
      L.inv ≫ CochainComplex.mappingCone.inr g.asHom := by
    simp [sq, coneSquareIso, CochainComplex.mappingCone.map]
  change CochainComplex.mappingCone.inr f ≫ (sq.inv ≫ en.inv ≫ LQ.hom) = _
  rw [← Category.assoc, hs]
  simp only [Category.assoc]
  rw [← Category.assoc (CochainComplex.mappingCone.inr g.asHom) en.inv LQ.hom, hi]
  have hn :
      ((ringedKoszulTensor O).obj I).map (ringedKoszulDualUnit O 1 (fun _ ↦ a) n) ≫
        LQ.hom = L.hom ≫ ringedKoszulDualUnit O 1 (fun _ ↦ a) n :=
    leftUnitor_naturality _
  rw [hn, Iso.inv_hom_id_assoc]

private theorem singleton_inverse_coordinates
    (a : (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O) (n : ℕ) :
    ∃ e : CochainComplex.mappingCone (ringedSingletonKoszulPower O a N n).asHom ≅
        ((ringedKoszulTensorTower O 1 (fun _ ↦ a)).obj N).obj (op n),
      (CochainComplex.mappingCone.inr _ ≫ e.hom =
        (ringedKoszulRightUnitIso O N).hom ≫
          ringedKoszulTensorUnitComponent O 1 (fun _ ↦ a) N (op n)) ∧
      (∀ q : ℤ, ∃ z : N.X (q + 1) ⟶
          ((curriedTensor _).obj (N.X (q + 1))).obj
            (((ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n)).X (-1)),
        (ringedKoszulRightUnitIso O N).inv.f (q + 1) ≫
          (CochainComplex.mappingCone.inl (ringedSingletonKoszulPower O a N n).asHom).v
            (q + 1) q (by omega) ≫ e.hom.f q =
          z ≫ HomologicalComplex.ιMapBifunctor N
            ((ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n))
            (curriedTensor _) (.up ℤ) (q + 1) (-1) q (by
              change q + 1 + -1 = q
              omega)) := by
  unfold ringedSingletonKoszulPower
  obtain ⟨c, hc⟩ := coefficient_cone O a n
  let I := ringedSiteRingComplex O
  let f : I ⟶ I := (HomologicalComplex.single _ (.up ℤ) 0).map
    (ringedKoszulScalar O a ^ (n + 1)).asHom
  let V := CochainComplex.mapBifunctorMappingCone₂Iso N f (curriedTensor _)
  let T := (ringedKoszulTensor O).obj N
  let e := V.symm ≪≫ T.mapIso c
  let R : HomologicalComplex.mapBifunctor N I (curriedTensor _) (.up ℤ) ≅ N :=
    ringedKoszulRightUnitIso O N
  let tc := HomologicalComplex.mapBifunctorMap (𝟙 N) c.hom (curriedTensor _) (.up ℤ)
  refine ⟨e, ?_, ?_⟩
  · change CochainComplex.mappingCone.inr _ ≫ (V.inv ≫ T.map c.hom) = _
    have hi : CochainComplex.mappingCone.inr _ ≫ V.inv =
        T.map (CochainComplex.mappingCone.inr f) := by
      exact CochainComplex.mapBifunctorMappingCone₂Iso.inr_inv N f (curriedTensor _)
    rw [← Category.assoc, hi, ← T.map_comp, hc]
    simp only [ringedKoszulTensorUnitComponent, Iso.hom_inv_id_assoc]
    rfl
  · intro q
    let z : N.X (q + 1) ⟶
        ((curriedTensor _).obj (N.X (q + 1))).obj
          (((ringedKoszulDualTower O 1 (fun _ ↦ a)).obj (op n)).X (-1)) :=
      (q + 1).negOnePow • ((ρ_ (N.X (q + 1))).inv ≫
        (N.X (q + 1) ◁ ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (CochainComplex.mappingCone.inl f).v 0 (-1) (by omega) ≫ c.hom.f (-1))))
    refine ⟨z, ?_⟩
    have hi :
        (CochainComplex.mappingCone.inl
          (HomologicalComplex.mapBifunctorMap (𝟙 N) f (curriedTensor _) (.up ℤ))).v
            (q + 1) q (by omega) ≫ V.inv.f q =
          (CochainComplex.mapBifunctorMappingCone₂Iso.ι₁ N f (curriedTensor _)).v
            (q + 1) q (by omega) := by
      simp [V, CochainComplex.mapBifunctorMappingCone₂Iso,
        CochainComplex.mapBifunctorMappingCone₂Iso.inv]
    change R.inv.f (q + 1) ≫
      (CochainComplex.mappingCone.inl
        (HomologicalComplex.mapBifunctorMap (𝟙 N) f (curriedTensor _) (.up ℤ))).v
          (q + 1) q (by omega) ≫ (V.inv.f q ≫ tc.f q) = _
    rw [← Category.assoc _ (V.inv.f q) (tc.f q), hi]
    have hU : R.inv.f (q + 1) =
        (ρ_ (N.X (q + 1))).inv ≫
          (N.X (q + 1) ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv) ≫
            HomologicalComplex.ιMapBifunctor N I (curriedTensor _) (.up ℤ)
              (q + 1) 0 (q + 1) (add_zero _) := by
      unfold R ringedKoszulRightUnitIso
      exact HomologicalComplex.rightUnitor'_inv N (q + 1)
    rw [hU]
    simp only [Category.assoc]
    rw [CochainComplex.mapBifunctorMappingCone₂Iso.ι_ι₁_assoc N f
      (curriedTensor _) (q + 1) 0 (q + 1) (add_zero _) q (by omega) (-1) (by omega)]
    dsimp only [tc]
    simp only [Category.assoc, Linear.units_smul_comp]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f]
    rw [(curriedTensor _).map_id]
    simp only [NatTrans.id_app, Category.id_comp]
    simp only [z, Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp,
      ← whiskerLeft_comp_assoc, curriedTensor_obj_map]

namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The singleton dual Koszul tensor has the two coordinates of the uniformizer cone.
This is a chain isomorphism before localization, without any flatness assumption on P.
The unshifted inclusion is the Koszul unit. The shifted inclusion factors through
Koszul degree -1, with its coefficient change and totalization sign absorbed into z.

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
finite free dual calculation; blueprint proposition-direct-image-along-open-immersion--1, Reduction
paragraph. (auxiliary; not a blueprint node).

Proof in words: multiplication by the constant uniformizer pi is monic on the
constant integer sheaf, since inverse image is exact. The locally principal kernel
of the first residue map is its image. The generating hypothesis gives locally
unique sections u and v with a=u*pi and pi=v*a. Cancellation of pi gives vu=1,
so commutativity makes u invertible. Uniqueness glues u and its inverse to global
sections. Thus a^(n+1)=u^(n+1)*pi^(n+1). Expand the singleton positive Koszul
complex, including its tensor with the empty factor O[0], by the right unitor.
Its dual is rank one in degrees -1 and zero, with the signed dual differential.
Tensoring it with complex(P) gives precisely P^q plus P^(q+1) in total degree q.
The balanced tensor identity for restriction of scalars identifies these summands
with the transported terms of P, even when P is not flat. On the unshifted
summand take the identity; on the shifted summand multiply by u^(-(n+1)) and
by the totalization sign that changes the dual differential into the usual cone
differential (dx+pi^(n+1)y,-dy). These maps and their inverses commute with the
differential, by the displayed scalar identity. The point coefficient comparison
and the section equivalence give exactly the functor modules used here. The
unshifted map is the dual projection evaluated at one, so it is the specified
Koszul tensor unit. The shifted map is the inverse rank-one identification,
unit multiplication and the indicated sign followed by the total-tensor inclusion
of bidegree (q+1,-1); call its first factor z. These are the two asserted formulas.
All operations are explicit finite sums, unitors and invertible scalar maps; zero
P and the empty scheme obey the same formulas. No quotient target, K-flatness,
quasi-isomorphism, transition map or inverse limit is used in this calculation. -/
theorem koszul_uniformizer_cone_coordinates
    (a : ((ring l E X).obj ⋙ forget CommRingCat).sections)
    (ha : ∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
      IsRingedIdealGeneratingList (ring l E X)
        (ConstantCompletion.kernelIdeal (residue l E X)).module
        (ConstantCompletion.kernelIdeal (residue l E X)).inclusion U 1
        (fun _ ↦ a.val (op U)))
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (b : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) b).down s =
        Padic.coefficientExtensionUniformizer l E * b.down s)
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ) :
    ∃ e : ((modules l E X).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mappingCone (PrincipalReduction.scalar l E X d n P)) ≅
          ((ringedKoszulTensorTower (ring l E X) 1 (fun _ ↦ a)).obj
            (complex l E X P)).obj (op n),
      (∀ q : ℤ,
        (modules l E X).map
            ((CochainComplex.mappingCone.inr (PrincipalReduction.scalar l E X d n P)).f q) ≫
          e.hom.f q =
        (ringedKoszulTensorUnitComponent (ring l E X) 1 (fun _ ↦ a)
          (complex l E X P) (op n)).f q) ∧
      (∀ q : ℤ, ∃ z : (modules l E X).obj (P.X (q + 1)) ⟶
          ((curriedTensor _).obj ((complex l E X P).X (q + 1))).obj
            (((ringedKoszulDualTower (ring l E X) 1 (fun _ ↦ a)).obj (op n)).X (-1)),
        (modules l E X).map
            ((CochainComplex.mappingCone.inl (PrincipalReduction.scalar l E X d n P)).v
              (q + 1) q (by omega)) ≫ e.hom.f q =
          z ≫ HomologicalComplex.ιMapBifunctor (complex l E X P)
            ((ringedKoszulDualTower (ring l E X) 1 (fun _ ↦ a)).obj (op n))
            (curriedTensor _) (.up ℤ) (q + 1) (-1) q (by
              change q + 1 + -1 = q
              omega)) := by
  obtain ⟨b, hb⟩ := uniformizer_koszul_scalar_square l E X a ha d hd P n
  obtain ⟨k, hk₀, hk₁⟩ := singleton_inverse_coordinates (ring l E X) a
    (complex l E X P) n
  exact transport_cone_coordinates (modules l E X)
    (End.of (PrincipalReduction.scalar l E X d n P))
    (ringedSingletonKoszulPower (ring l E X) a (complex l E X P) n)
    b (ringedKoszulRightUnitIso (ring l E X) (complex l E X P)) hb k
    (ringedKoszulTensorUnitComponent (ring l E X) 1 (fun _ ↦ a)
      (complex l E X P) (op n))
    (fun q ↦ ((curriedTensor _).obj ((complex l E X P).X (q + 1))).obj
      (((ringedKoszulDualTower (ring l E X) 1 (fun _ ↦ a)).obj (op n)).X (-1)))
    (fun q ↦ HomologicalComplex.ιMapBifunctor (complex l E X P)
      ((ringedKoszulDualTower (ring l E X) 1 (fun _ ↦ a)).obj (op n))
      (curriedTensor _) (.up ℤ) (q + 1) (-1) q (by
        change q + 1 + -1 = q
        omega)) hk₀ hk₁
end AlgebraicGeometry.ProEtale.InternalCompletionTransport

end Ringed
