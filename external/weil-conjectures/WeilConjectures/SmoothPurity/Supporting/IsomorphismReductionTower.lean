/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Isomorphism inverse image of completed coefficient reduction towers

Source: blueprint main-20261015, ordinary compact cohomology, coefficient paragraph;
Stacks Tags 03EL, 03EK, 06YS, 06YY and 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower).
Index n denotes the positive exponent n+1. Inverse image is the recorded sectionwise
model of the site equivalence, with its module action transported by the inverse
of the canonical coefficient map. All coefficients have size max u (t+1).

## Main definitions and statements

- `isoReductionCompletedMap`: the limit coefficient isomorphism fixed by projections.
- `isoReductionIntegralInverse`, `isoReductionFiniteInverse`: recorded inverse image
  with scalar action transported through the canonical ring isomorphisms.
- `isomorphismReductionTower`: normalized complex isomorphisms, quotient and
  transition identities, naturality and canonical resolution compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
universe t u r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence scalarReductionExtension
  scalarReductionDerivedExtension scalarReductionCounit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- Abelian sheafification in a coefficient universe containing the site.
Source: Stacks Tag 03DA
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
instance (priority := 4000) isoReductionAbSheafify (W : Scheme.{t})
    [EssentiallySmall.{r} W.ProEt] :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{r} :=
  SheafOfModules.hasSheafify_coefficientUniverse

/-- The local-bijection criterion in the same coefficient universe.
Source: Stacks Tag 03DA
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
instance (priority := 4000) isoReductionAbBijective (W : Scheme.{t})
    [EssentiallySmall.{r} W.ProEt] :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{r} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- The site has a small model in the explicit coefficient universe.
Source: blueprint size convention
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
instance (priority := 4000) isoReductionSiteSmall (W : Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf _

private theorem pointwisePostcomposeEquivalence
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (G : B ⥤ D) [G.IsEquivalence] (F : A ⥤ B) (L : A ⥤ C) :
    G.PreservesPointwiseRightKanExtension F L := fun c ↦ by
  let H := StructuredArrow.proj c L ⋙ F
  let : PreservesLimit H G :=
    (Adjunction.isEquivalencePreservesLimits G).preservesLimitsOfShape.preservesLimit
  exact Functor.preservesPointwiseRightKanExtensionAtOfPreservesLimit _ _ _ c

section TensorLinearity
universe a b v
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]
private theorem transportedTensor_smul
    {R S : Sheaf J CommRingCat.{v}} (c : R ⟶ S)
    (M : SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (h : N = SheafOfModules.changeOfRings c M) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom h.symm).val.app U
      (SheafOfModules.UnrestrictedTowerProof.tensorSection c M U s x) =
      s • (eqToHom h.symm).val.app U
        (SheafOfModules.UnrestrictedTowerProof.tensorSection c M U 1 x) := by
  let a := ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (SheafOfModules.changeOfRingsPresheaf c M)).app U
  let b := (eqToHom h.symm).val.app U
  change b (a (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
    s • b (a ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))
  rw [← b.hom.map_smul, ← a.hom.map_smul]
  change b (a (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
    b (a ((s * 1) ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))
  rw [mul_one]
end TensorLinearity

private theorem adjointSquare
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (F : A ⥤ C) (G : B ⥤ D) [F.Full] [F.Faithful] [G.IsEquivalence]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : R ⋙ F ≅ G ⋙ R') :
    ∃ e : F ⋙ L' ≅ L ⋙ G, ∀ M,
      adj'.unit.app (F.obj M) ≫ R'.map (e.hom.app M) =
        F.map (adj.unit.app M) ≫ s.hom.app (L.obj M) := by
  let δ : F ⋙ L' ⟶ L ⋙ G :=
    { app := fun M ↦ (adj'.homEquiv _ _).symm
        (F.map (adj.unit.app M) ≫ s.hom.app (L.obj M))
      naturality := by
        intro M N f
        apply (adj'.homEquiv _ _).injective
        change adj'.homEquiv _ _ (L'.map (F.map f) ≫ _) =
          adj'.homEquiv _ _ (_ ≫ G.map (L.map f))
        dsimp only [Functor.comp_obj]
        rw [adj'.homEquiv_naturality_left, adj'.homEquiv_naturality_right]
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        change F.map f ≫ (F.map (adj.unit.app N) ≫ s.hom.app (L.obj N)) =
          (F.map (adj.unit.app M) ≫ s.hom.app (L.obj M)) ≫ R'.map (G.map (L.map f))
        calc
          _ = F.map (f ≫ adj.unit.app N) ≫ s.hom.app (L.obj N) := by
            rw [F.map_comp, Category.assoc]
          _ = F.map (adj.unit.app M ≫ R.map (L.map f)) ≫ s.hom.app (L.obj N) := by
            rw [show f ≫ adj.unit.app N = adj.unit.app M ≫ R.map (L.map f) from
              adj.unit.naturality f]
          _ = _ := by
            rw [F.map_comp, Category.assoc, Category.assoc]
            exact congrArg (F.map (adj.unit.app M) ≫ ·)
              (s.hom.naturality (L.map f)) }
  have hδ (M : A) (N : B) (f : L.obj M ⟶ N) :
      δ.app M ≫ G.map f = (adj'.homEquiv _ _).symm
        (F.map (adj.homEquiv _ _ f) ≫ s.hom.app N) := by
    apply (adj'.homEquiv _ _).injective
    rw [adj'.homEquiv_naturality_right]
    change adj'.homEquiv _ _ ((adj'.homEquiv _ _).symm _) ≫ R'.map (G.map f) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hn := s.hom.naturality f
    change F.map (R.map f) ≫ s.hom.app N = s.hom.app (L.obj M) ≫ R'.map (G.map f) at hn
    rw [Category.assoc, ← hn]
    simp only [adj.homEquiv_unit, F.map_comp, Category.assoc]
  have hb (M : A) (N : B) :
      Function.Bijective (fun f : G.obj (L.obj M) ⟶ G.obj N ↦ δ.app M ≫ f) := by
    let k : (L.obj M ⟶ N) ≃ (L'.obj (F.obj M) ⟶ G.obj N) :=
      (adj.homEquiv _ _).trans
        (((Functor.FullyFaithful.ofFullyFaithful F).homEquiv).trans
          ((Iso.homCongr (Iso.refl _) (s.app N)).trans (adj'.homEquiv _ _).symm))
    have hk : (fun f : L.obj M ⟶ N ↦ δ.app M ≫ G.map f) = k := by
      funext f
      simpa [k, Iso.homCongr] using hδ M N f
    constructor
    · intro f g h
      obtain ⟨f, rfl⟩ := G.map_surjective f
      obtain ⟨g, rfl⟩ := G.map_surjective g
      apply congrArg G.map
      apply k.injective
      exact (congrFun hk f).symm.trans (h.trans (congrFun hk g))
    · intro f
      obtain ⟨g, hg⟩ := k.surjective f
      exact ⟨G.map g, (congrFun hk g).trans hg⟩
  have hi (M : A) : IsIso (δ.app M) := by
    apply isIso_of_coyoneda_map_bijective
    intro N
    let e := G.objObjPreimageIso N
    let k : (G.obj (L.obj M) ⟶ N) ≃ (L'.obj (F.obj M) ⟶ N) :=
      (Iso.homCongr (Iso.refl _) e.symm).trans
        ((Equiv.ofBijective _ (hb M (G.objPreimage N))).trans
          (Iso.homCongr (Iso.refl _) e))
    change Function.Bijective (fun f : G.obj (L.obj M) ⟶ N ↦ δ.app M ≫ f)
    have hk : (fun f : G.obj (L.obj M) ⟶ N ↦ δ.app M ≫ f) = k := by
      funext f
      simp [k, Category.assoc]
    rw [hk]
    exact k.bijective
  have : IsIso δ := NatIso.isIso_of_isIso_app δ
  exact ⟨asIso δ, fun M ↦ (adj'.homEquiv _ _).apply_symm_apply _⟩

private theorem comparisonOfUniversal
    {C D H C' D' H' : Type*}
    [Category* C] [Category* D] [Category* H]
    [Category* C'] [Category* D'] [Category* H']
    (Q : C ⥤ D) (Q' : C' ⥤ D') (F : C ⥤ C') (DF : D ⥤ D') (G : H ⥤ H')
    (E : C ⥤ H) (E' : C' ⥤ H') (T : D ⥤ H) (T' : D' ⥤ H')
    (ε : Q ⋙ T ⟶ E) (ε' : Q' ⋙ T' ⟶ E')
    (i : F ⋙ Q' ≅ Q ⋙ DF) (j : E ⋙ G ≅ F ⋙ E')
    [(T ⋙ G).IsRightKanExtension
      ((Functor.associator Q T G).inv ≫ Functor.whiskerRight ε G)]
    {P P' K : C} (q : P ⟶ K) (q' : P' ⟶ K)
    [_hQq : IsIso (Q.map q)] [hQq' : IsIso (Q.map q')]
    [_hFq : IsIso (Q'.map (F.map q))] [hFq' : IsIso (Q'.map (F.map q'))]
    [hεP : IsIso (ε.app P)] [_hεP' : IsIso (ε.app P')]
    [hεFP : IsIso (ε'.app (F.obj P))] [_hεFP' : IsIso (ε'.app (F.obj P'))] :
    G.map (inv (ε.app P) ≫ T.map (Q.map q) ≫
        inv (T.map (Q.map q')) ≫ ε.app P') ≫ j.hom.app P' =
      j.hom.app P ≫ inv (ε'.app (F.obj P)) ≫ T'.map (Q'.map (F.map q)) ≫
        inv (T'.map (Q'.map (F.map q'))) ≫ ε'.app (F.obj P') := by
  let α := (Functor.associator Q T G).inv ≫ Functor.whiskerRight ε G
  let β : Q ⋙ (DF ⋙ T') ⟶ E ⋙ G :=
    (Functor.associator Q DF T').inv ≫ Functor.whiskerRight i.inv T' ≫
      (Functor.associator F Q' T').hom ≫ Functor.whiskerLeft F ε' ≫ j.inv
  let δ : DF ⋙ T' ⟶ T ⋙ G := (T ⋙ G).liftOfIsRightKanExtension α _ β
  have hd (A : C) : δ.app (Q.obj A) ≫ G.map (ε.app A) ≫ j.hom.app A =
      T'.map (i.inv.app A) ≫ ε'.app (F.obj A) := by
    have h := (T ⋙ G).liftOfIsRightKanExtension_fac_app α (DF ⋙ T') β A
    dsimp only [α, β, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id] at h
    simp only [Category.id_comp] at h
    change δ.app (Q.obj A) ≫ G.map (ε.app A) =
      T'.map (i.inv.app A) ≫ ε'.app (F.obj A) ≫ j.inv.app A at h
    rw [← Category.assoc, h]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact congrArg (T'.map (i.inv.app A) ≫ ·)
      (Category.comp_id (ε'.app (F.obj A)))
  have hn (A B : C) (f : A ⟶ B) :
      T'.map (Q'.map (F.map f)) ≫ T'.map (i.hom.app B) ≫ δ.app (Q.obj B) =
        T'.map (i.hom.app A) ≫ δ.app (Q.obj A) ≫ G.map (T.map (Q.map f)) := by
    have hi := i.hom.naturality f
    change Q'.map (F.map f) ≫ i.hom.app B = i.hom.app A ≫ DF.map (Q.map f) at hi
    rw [← T'.map_comp_assoc, hi, T'.map_comp, Category.assoc]
    exact congrArg (T'.map (i.hom.app A) ≫ ·) (δ.naturality (Q.map f))
  have hd' (A : C) :
      T'.map (i.hom.app A) ≫ δ.app (Q.obj A) ≫ G.map (ε.app A) ≫ j.hom.app A =
        ε'.app (F.obj A) := by
    rw [hd, ← T'.map_comp_assoc]
    simp only [Iso.hom_inv_id_app, T'.map_id, Category.id_comp]
  let k (A : C) := T'.map (i.hom.app A) ≫ δ.app (Q.obj A)
  have hk (A : C) : k A ≫ G.map (ε.app A) ≫ j.hom.app A = ε'.app (F.obj A) := by
    simpa only [k, Category.assoc] using hd' A
  have hk' (A : C) [IsIso (ε.app A)] :
      k A = ε'.app (F.obj A) ≫ j.inv.app A ≫ inv (G.map (ε.app A)) := by
    apply (cancel_mono (G.map (ε.app A) ≫ j.hom.app A)).1
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.inv_hom_id_app]
    exact (hk A).trans (Category.comp_id (ε'.app (F.obj A))).symm
  have hkq (A B : C) (f : A ⟶ B) :
      T'.map (Q'.map (F.map f)) ≫ k B = k A ≫ G.map (T.map (Q.map f)) := by
    simpa only [k, Category.assoc] using hn A B f
  have hh :
      T'.map (Q'.map (F.map q)) ≫ inv (T'.map (Q'.map (F.map q'))) ≫ k P' =
        k P ≫ G.map (T.map (Q.map q)) ≫ inv (G.map (T.map (Q.map q'))) := by
    have hq' : inv (T'.map (Q'.map (F.map q'))) ≫ k P' =
        k K ≫ inv (G.map (T.map (Q.map q'))) := by
      apply (cancel_epi (T'.map (Q'.map (F.map q')))).1
      simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
      rw [hkq]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [hq', ← Category.assoc, hkq, Category.assoc]
  apply (cancel_epi (ε'.app (F.obj P) ≫ j.inv.app P)).1
  calc
    _ = k P ≫ G.map (T.map (Q.map q)) ≫ inv (G.map (T.map (Q.map q'))) ≫
        G.map (ε.app P') ≫ j.hom.app P' := by
      rw [hk' P]
      simp only [G.map_comp, Functor.map_inv, Category.assoc]
    _ = T'.map (Q'.map (F.map q)) ≫ inv (T'.map (Q'.map (F.map q'))) ≫
        k P' ≫ G.map (ε.app P') ≫ j.hom.app P' := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ G.map (ε.app P') ≫ j.hom.app P') hh.symm
    _ = T'.map (Q'.map (F.map q)) ≫ inv (T'.map (Q'.map (F.map q'))) ≫
        ε'.app (F.obj P') := by rw [hk]
    _ = _ := by
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id_assoc]

private theorem comparisonOfUniversalWithFormulas
    {C D H C' D' H' : Type*}
    [Category* C] [Category* D] [Category* H]
    [Category* C'] [Category* D'] [Category* H']
    (Q : C ⥤ D) (Q' : C' ⥤ D') (F : C ⥤ C') (DF : D ⥤ D') (G : H ⥤ H')
    (E : C ⥤ H) (E' : C' ⥤ H') (T : D ⥤ H) (T' : D' ⥤ H')
    (ε : Q ⋙ T ⟶ E) (ε' : Q' ⋙ T' ⟶ E')
    (i : F ⋙ Q' ≅ Q ⋙ DF) (j : E ⋙ G ≅ F ⋙ E')
    [(T ⋙ G).IsRightKanExtension
      ((Functor.associator Q T G).inv ≫ Functor.whiskerRight ε G)]
    {P P' K : C} (q : P ⟶ K) (q' : P' ⟶ K)
    [_hQq : IsIso (Q.map q)] [hQq' : IsIso (Q.map q')]
    [_hFq : IsIso (Q'.map (F.map q))] [hFq' : IsIso (Q'.map (F.map q'))]
    [hεP : IsIso (ε.app P)] [_hεP' : IsIso (ε.app P')]
    [hεFP : IsIso (ε'.app (F.obj P))] [_hεFP' : IsIso (ε'.app (F.obj P'))]
    (c : E.obj P ⟶ E.obj P') (c' : E'.obj (F.obj P) ⟶ E'.obj (F.obj P'))
    (hc : c = inv (ε.app P) ≫ T.map (Q.map q) ≫
      inv (T.map (Q.map q')) ≫ ε.app P')
    (hc' : c' = inv (ε'.app (F.obj P)) ≫ T'.map (Q'.map (F.map q)) ≫
      inv (T'.map (Q'.map (F.map q'))) ≫ ε'.app (F.obj P')) :
    G.map c ≫ j.hom.app P' = j.hom.app P ≫ c' := by
  rw [hc, hc']
  exact comparisonOfUniversal Q Q' F DF G E E' T T' ε ε' i j q q'

private theorem conjugatedComparison
    {A : Type*} [Category* A]
    {a a' b b' c c' : A} (u : a ≅ b) (u' : a' ≅ b') (f : a ⟶ a') (h : c ⟶ c')
    (v : b ⟶ c) (v' : b' ⟶ c')
    (j : a ⟶ c) (j' : a' ⟶ c')
    (hj : j = u.hom ≫ v) (hj' : j' = u'.hom ≫ v')
    (eq : f ≫ j' = j ≫ h) :
    (u.inv ≫ f ≫ u'.hom) ≫ v' = v ≫ h := by
  rw [hj, hj'] at eq
  apply (cancel_epi u.hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using eq

private theorem moduleIso_hom_inv_apply
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {M N : SheafOfModules.{r} R}
    (e : M ≅ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    e.inv.val.app U (e.hom.val.app U x) = x := by
  exact congrArg (fun f : M ⟶ M ↦ f.val.app U x) e.hom_inv_id

private theorem restrictionMap_apply
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (p : R ⟶ S)
    {M N : SheafOfModules.{r} S} (f : M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((SheafOfModules.restrictScalars p).map f).val.app U x = f.val.app U x := rfl

private theorem restrictionSquare
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {R A : Sheaf K RingCat.{r}} {S B : Sheaf J RingCat.{r}}
    (c : (F.sheafPushforwardContinuous RingCat.{r} J K).obj R ≅ S)
    (d : (F.sheafPushforwardContinuous RingCat.{r} J K).obj A ≅ B)
    (p : R ⟶ A) (q : S ⟶ B)
    (h : c.hom ≫ q = (F.sheafPushforwardContinuous RingCat.{r} J K).map p ≫ d.hom) :
    ∃ s : SheafOfModules.restrictScalars.{r} p ⋙ SheafOfModules.pushforward.{r} c.inv ≅
        SheafOfModules.pushforward.{r} d.inv ⋙ SheafOfModules.restrictScalars.{r} q,
      ∀ (N : SheafOfModules.{r} A) (U : Cᵒᵖ) (x : N.val.obj (F.op.obj U)),
        (s.hom.app N).val.app U x = x := by
  have he : c.inv ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map p = q ≫ d.inv := by
    calc
      _ = c.inv ≫ ((F.sheafPushforwardContinuous RingCat.{r} J K).map p ≫ d.hom) ≫
          d.inv := by simp only [Category.assoc, d.hom_inv_id, Category.comp_id]
      _ = c.inv ≫ (c.hom ≫ q) ≫ d.inv := by rw [h]
      _ = _ := by simp only [← Category.assoc, c.inv_hom_id, Category.id_comp]
  let a := SheafOfModules.pushforwardComp.{r} (F := F) (G := 𝟭 D)
    (J := J) (K := K) (K' := K) c.inv p
  let b := SheafOfModules.pushforwardComp.{r} (F := 𝟭 C) (G := F)
    (J := J) (K := J) (K' := K) q d.inv
  let s := a ≪≫ SheafOfModules.pushforwardCongr.{r} he ≪≫ b.symm
  refine ⟨s, ?_⟩
  intro N U x
  rfl

private theorem isoReduction_equivalence
    {RY : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj RY ⟶ RX)
    [IsIso c] : (isoSectionwiseModuleInverseImage g c).IsEquivalence := by
  let F := proEtaleIsoPostcompose g
  let G := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt :=
    CategoryTheory.Equivalence.mk F G e.2.1.some.symm e.2.2.1.some
  have : E.functor.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous g
  have : E.inverse.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    proEtaleIsoPostcompose_isContinuous (inv g)
  let adj := E.toAdjunction
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{max u (t + 1)})
    (ProEt.topology X) (ProEt.topology Y)
  let φ := inv c
  let ψ : RY ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj RX :=
    shAdj.unit.app RY ≫ (G.sheafPushforwardContinuous _ _ _).map c
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    simp [ψ, φ, shAdj, adj]
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (E.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((E.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((E.functor.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c := congrArg (fun h ↦ φ ≫ h ≫ c) ht
        _ = _ := by simp [φ]
    exact congrArg (fun f ↦ f.hom) hh
  let EM := SheafOfModules.pushforwardPushforwardEquivalence E φ ψ H₁ H₂
  exact EM.isEquivalence_functor

private theorem isoReductionConstant_hom_ext (W : Scheme.{t})
    (A B : CommRingCat.{max u (t + 1)})
    (f h : (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj A) ⟶
      (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj B))
    (hf : ∀ (U : W.ProEt) (a : A),
      f.hom.app (op U)
          ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app
            (op U) a) =
        h.hom.app (op U)
          ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app
            (op U) a)) : f = h := by
  let S := sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have he : S.preimage f = S.preimage h := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology W) _ _
      ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj B).property
    ext U a
    have ef := congrArg (fun z ↦ z.hom.app U) (S.map_preimage f)
    have eh := congrArg (fun z ↦ z.hom.app U) (S.map_preimage h)
    change ((S.map (S.preimage f)).hom.app U) _ =
      ((S.map (S.preimage h)).hom.app U) _
    rw [ef, eh]
    exact hf U.unop a
  simpa only [S.map_preimage] using congrArg S.map he

private theorem isoReductionConstant_map (W : Scheme.{t})
    {A B : CommRingCat.{max u (t + 1)}} (f : A ⟶ B) (U : W.ProEt) (a : A) :
    (((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).map f).hom.app (op U))
        (((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app
          (op U)) a) =
      ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj B)).app
        (op U)) (f a) := by
  exact (congrArg (fun e ↦ (e.app (op U)) a)
    (toSheafify_naturality (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).map f))).symm

private theorem isoReductionConstant_naturality
    {A B : CommRingCat.{max u (t + 1)}} (f : A ⟶ B) :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map f)) ≫
      isoSectionwiseConstantMap g B =
    isoSectionwiseConstantMap g A ≫
      (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map f) := by
  let cA := isoSectionwiseConstantMap g A
  let cB := isoSectionwiseConstantMap g B
  have hA := (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec
  have hB := (isoSectionwiseConstantMap_existsUnique g B).exists.choose_spec
  apply (cancel_epi (inv cA)).1
  apply isoReductionConstant_hom_ext X A B
  intro U a
  have hi : (inv cA).hom.app (op U)
      ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app (op U) a) =
      (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose g).obj U)) a := by
    rw [← hA U a]
    exact congrArg (fun e ↦ e.hom.app (op U)
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose g).obj U)) a)) (IsIso.hom_inv_id cA)
  change cB.hom.app (op U)
      ((((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map f).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)))
          ((inv cA).hom.app (op U) _)) =
    (((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map f).hom.app (op U))
      (cA.hom.app (op U) ((inv cA).hom.app (op U) _))
  erw [hi, isoReductionConstant_map, hB, hA, isoReductionConstant_map]

/-- The completed coefficient comparison is uniquely specified by its projections.
Source: Stacks Tags 09A5, 03CO
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower).
Proof: inverse image preserves the limit by the recorded site equivalence. The
constant comparisons commute with coefficient reductions by their normalization
on constants. Their inverse-limit comparison is invertible, has the displayed
projections, and is unique because limit projections are jointly monic. -/
theorem isoReductionCompletedMap_existsUnique :
    ∃! c : (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ≅
        completedIntegralCoefficientSheafUnrestricted l E X,
      ∀ n : ℕ, c.hom ≫ limit.π (integralCoefficientSheafSystem l E X) (op n) =
        (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
          (limit.π (integralCoefficientSheafSystem l E Y) (op n)) ≫
          isoSectionwiseConstantMap g
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let F := isoSectionwiseInverseImage g RingCat.{max u (t + 1)}
  let A := integralCoefficientSheafSystem l E Y
  let B := integralCoefficientSheafSystem l E X
  let α : A ⋙ F ⟶ B := NatTrans.ofOpSequence
    (fun n ↦ isoSectionwiseConstantMap g
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (fun n ↦ by
      simp only [Functor.comp_map, A, B, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact isoReductionConstant_naturality g _)
  have : ∀ n, IsIso (α.app n) := fun n ↦ isoSectionwiseConstantMap_isIso g _
  let e : A ⋙ F ≅ B := NatIso.ofComponents (fun n ↦ asIso (α.app n))
    (fun f ↦ α.naturality f)
  have : PreservesLimitsOfSize.{0, 0} F :=
    (isoSectionwiseInverseImage_equivalence g RingCat.{max u (t + 1)}).2.1
  let d : F.obj (limit A) ≅ limit B :=
    preservesLimitIso F A ≪≫ HasLimit.isoOfNatIso e
  have hd : ∀ n : ℕ, d.hom ≫ limit.π B (op n) =
      F.map (limit.π A (op n)) ≫ α.app (op n) := by
    intro n
    simp only [d, Iso.trans_hom, Category.assoc,
      HasLimit.isoOfNatIso_hom_π, preservesLimitIso_hom_π_assoc, e,
      NatIso.ofComponents_hom_app, asIso_hom]
  refine ⟨d, hd, ?_⟩
  intro c hc
  apply Iso.ext
  apply (limit.isLimit B).hom_ext
  intro n
  exact (hc n.unop).trans (hd n.unop).symm

/-- The actual limit comparison followed by the limit of constant comparisons.
Source: Stacks Tag 03CO
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
def isoReductionCompletedMap :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ≅
      completedIntegralCoefficientSheafUnrestricted l E X :=
  (isoReductionCompletedMap_existsUnique l E g).exists.choose

/-- Relabelling with scalar action transported along the completed comparison.
Source: Stacks Tags 00WX, 03D2
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
abbrev isoReductionIntegralInverse :
    scalarReductionSource l E Y ⥤ scalarReductionSource l E X :=
  isoSectionwiseModuleInverseImage g (isoReductionCompletedMap l E g).hom

/-- Relabelling over the positive finite coefficient quotient.
Source: Stacks Tags 00WX, 03D2
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
abbrev isoReductionFiniteInverse (n : ℕ) :
    scalarReductionTarget l E Y n ⥤ scalarReductionTarget l E X n :=
  isoSectionwiseModuleInverseImage g (isoSectionwiseConstantMap g
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

/-- Exactness of finite inverse image, using the recorded independent-size interface.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
instance isoReductionFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (isoReductionFiniteInverse l E g n) :=
  isoSectionwiseModuleInverseImage_limits.{t, u} g _

/-- Exactness of finite inverse image, using the recorded independent-size interface.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
instance isoReductionFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (isoReductionFiniteInverse l E g n) :=
  isoSectionwiseModuleInverseImage_colimits.{t, u} g _

/-- The completed inverse image applied termwise.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
abbrev isoReductionIntegralComplex :=
  (isoReductionIntegralInverse l E g).mapHomologicalComplex (.up ℤ)

/-- The finite inverse image applied termwise.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
abbrev isoReductionFiniteComplex (n : ℕ) :=
  (isoReductionFiniteInverse l E g n).mapHomologicalComplex (.up ℤ)

private theorem isoReduction_projection_eq (W : Scheme.{t}) (n : ℕ) :
    (sheafCompose (ProEt.topology W) (forget₂ CommRingCat RingCat)).map
      (completedIntegralCommRingProjectionUnrestricted l E W n) =
        limit.π (integralCoefficientSheafSystem l E W) (op n) := by
  rfl

private theorem isoReduction_completedProjectionSquare (n : ℕ) :
    (isoReductionCompletedMap l E g).hom ≫
        (sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).map
          (completedIntegralCommRingProjectionUnrestricted l E X n) =
      (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map
          (completedIntegralCommRingProjectionUnrestricted l E Y n)) ≫
        isoSectionwiseConstantMap g (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  simpa only [isoReduction_projection_eq, isoReductionCompletedMap] using
    (isoReductionCompletedMap_existsUnique l E g).exists.choose_spec n

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  isoReductionCompletedMap isoSectionwiseConstantMap

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isoReduction_restrictionSquare (n : ℕ) :
    ∃ s : scalarReductionRestriction l E Y n ⋙ isoReductionIntegralInverse l E g ≅
      isoReductionFiniteInverse l E g n ⋙ scalarReductionRestriction l E X n,
      ∀ (N : scalarReductionTarget l E Y n) (U : X.ProEtᵒᵖ)
        (x : N.val.obj ((proEtaleIsoPostcompose g).op.obj U)),
        (s.hom.app N).val.app U x = x := by
  let πY : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
      integralCoefficientSheaf l E Y n := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat RingCat)).map (completedIntegralCommRingProjectionUnrestricted l E Y n)
  let πX : completedIntegralCoefficientSheafUnrestricted l E X ⟶
      integralCoefficientSheaf l E X n := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat RingCat)).map (completedIntegralCommRingProjectionUnrestricted l E X n)
  have h : (isoReductionCompletedMap l E g).hom ≫ πX =
      (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map πY ≫
        isoSectionwiseConstantMap g (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    isoReduction_completedProjectionSquare l E g n
  exact restrictionSquare (R := completedIntegralCoefficientSheafUnrestricted l E Y)
    (S := completedIntegralCoefficientSheafUnrestricted l E X)
    (A := integralCoefficientSheaf l E Y n) (B := integralCoefficientSheaf l E X n)
    (proEtaleIsoPostcompose g)
    (asIso (isoReductionCompletedMap l E g).hom) (asIso (isoSectionwiseConstantMap g
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))) πY πX h

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[irreducible] private def isoReduction_adj (W : Scheme.{t}) (n : ℕ) :
    scalarReductionExtension l E W n ⊣ scalarReductionRestriction l E W n :=
  (scalarReductionExtension_adjunction l E W n).choose

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem isoReduction_tensorSquare (n : ℕ) :
    ∃ e : scalarReductionExtension l E Y n ⋙ isoReductionFiniteInverse l E g n ≅
        isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n,
      ∀ M, (isoReductionIntegralInverse l E g).map
          ((isoReduction_adj l E Y n).unit.app M) ≫
        (isoReduction_restrictionSquare l E g n).choose.hom.app
          ((scalarReductionExtension l E Y n).obj M) ≫
        (scalarReductionRestriction l E X n).map (e.hom.app M) =
      (isoReduction_adj l E X n).unit.app
        ((isoReductionIntegralInverse l E g).obj M) := by
  classical
  let F := isoReductionIntegralInverse l E g
  let G := isoReductionFiniteInverse l E g n
  let : F.IsEquivalence := isoReduction_equivalence.{t, u} g
    (isoReductionCompletedMap l E g).hom
  let : G.IsEquivalence := isoReduction_equivalence.{t, u} g
    (isoSectionwiseConstantMap g (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
  let s := (isoReduction_restrictionSquare l E g n).choose
  obtain ⟨e, he⟩ := adjointSquare F G
    (L := scalarReductionExtension l E Y n) (R := scalarReductionRestriction l E Y n)
    (L' := scalarReductionExtension l E X n) (R' := scalarReductionRestriction l E X n)
    (isoReduction_adj l E Y n)
    (isoReduction_adj l E X n) s
  refine ⟨e.symm, ?_⟩
  intro M
  rw [← Category.assoc, ← he M]
  simp only [Iso.symm_hom, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Functor.comp_obj]
  rw [(scalarReductionRestriction l E X n).map_id, Category.comp_id]

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem isoReduction_tensorUnit (n : ℕ)
    (e : scalarReductionExtension l E Y n ⋙ isoReductionFiniteInverse l E g n ≅
      isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n)
    (he : ∀ M, (isoReductionIntegralInverse l E g).map
        ((isoReduction_adj l E Y n).unit.app M) ≫
      (isoReduction_restrictionSquare l E g n).choose.hom.app
        ((scalarReductionExtension l E Y n).obj M) ≫
      (scalarReductionRestriction l E X n).map (e.hom.app M) =
        (isoReduction_adj l E X n).unit.app
          ((isoReductionIntegralInverse l E g).obj M))
    (M : scalarReductionSource l E Y) (U : X.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
    (e.hom.app M).val.app U
      (show ((isoReductionFiniteInverse l E g n).obj
        ((scalarReductionExtension l E Y n).obj M)).val.obj U from
          ((isoReduction_adj l E Y n).unit.app M).val.app ((proEtaleIsoPostcompose g).op.obj U) x) =
      ((isoReduction_adj l E X n).unit.app
        ((isoReductionIntegralInverse l E g).obj M)).val.app U x := by
  have h := congrArg (fun f ↦ f.val.app U x) (he M)
  change (e.hom.app M).val.app U
    (((isoReduction_restrictionSquare l E g n).choose.hom.app _).val.app U
      (((isoReduction_adj l E Y n).unit.app M).val.app
        ((proEtaleIsoPostcompose g).op.obj U) x)) =
        ((isoReduction_adj l E X n).unit.app
          ((isoReductionIntegralInverse l E g).obj M)).val.app U x at h
  rw [(isoReduction_restrictionSquare l E g n).choose_spec] at h
  exact h

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem isoReduction_extension_obj (W : Scheme.{t}) (n : ℕ)
    (M : scalarReductionSource l E W) :
    (scalarReductionExtension l E W n).obj M = SheafOfModules.changeOfRings
      (completedIntegralCommRingProjectionUnrestricted l E W n) M := by
  unfold scalarReductionExtension
  exact (scalarReductionExistence l E W n).choose_spec.choose M

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [local semireducible] scalarReductionExtension scalarReductionExistence
  unrestrictedIntegralReductionExistence in
private theorem isoReduction_tensorSection_eq (W : Scheme.{t}) (n : ℕ)
    (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : M.val.obj U) :
    (eqToHom (isoReduction_extension_obj l E W n M).symm).val.app U
      (SheafOfModules.UnrestrictedTowerProof.tensorSection
        (completedIntegralCommRingProjectionUnrestricted l E W n) M U s x) =
      unrestrictedTowerTensorSection l E W n M U s x := by
  unfold SheafOfModules.UnrestrictedTowerProof.tensorSection unrestrictedTowerTensorSection
    unrestrictedIntegralTensorSection
  rfl

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem isoReduction_tensor_smul (W : Scheme.{t}) (n : ℕ)
    (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E W n).obj.obj U) (x : M.val.obj U) :
    unrestrictedTowerTensorSection l E W n M U s x =
      s • unrestrictedTowerTensorSection l E W n M U 1 x := by
  rw [← isoReduction_tensorSection_eq l E W n M U s x,
    ← isoReduction_tensorSection_eq l E W n M U 1 x]
  exact transportedTensor_smul
    (completedIntegralCommRingProjectionUnrestricted l E W n) M
    ((scalarReductionExtension l E W n).obj M)
    (isoReduction_extension_obj l E W n M) U s x

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem isoReduction_tensorFormula (n : ℕ)
    (e : scalarReductionExtension l E Y n ⋙ isoReductionFiniteInverse l E g n ≅
      isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n)
    (he : ∀ (M : scalarReductionSource l E Y) (U : X.ProEtᵒᵖ)
      (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)),
      (e.hom.app M).val.app U
        (((isoReduction_adj l E Y n).unit.app M).val.app
          ((proEtaleIsoPostcompose g).op.obj U) x) =
      (((isoReduction_adj l E X n).unit.app
        ((isoReductionIntegralInverse l E g).obj M)).val.app U x))
    (M : scalarReductionSource l E Y) (U : X.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      ((proEtaleIsoPostcompose g).op.obj U))
    (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
    (e.hom.app M).val.app U
      (unrestrictedTowerTensorSection l E Y n M
        ((proEtaleIsoPostcompose g).op.obj U) s x) =
      unrestrictedTowerTensorSection l E X n ((isoReductionIntegralInverse l E g).obj M) U
        ((isoSectionwiseConstantMap g (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app U s) x := by
  let d := isoSectionwiseConstantMap g (CommRingCat.of
    (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  have hi : (inv d).hom.app U (d.hom.app U s) = s :=
    congrArg (fun f ↦ f.hom.app U s) (IsIso.hom_inv_id d)
  have hu (W : Scheme.{t}) (N : scalarReductionSource l E W) (V : W.ProEtᵒᵖ)
      (y : N.val.obj V) :
      ((isoReduction_adj l E W n).unit.app N).val.app V y =
        unrestrictedTowerTensorSection l E W n N V 1 y := by
    rw [isoReduction_adj, (scalarReductionExtension_adjunction l E W n).choose_spec]
    rfl
  have hh := he M U x
  rw [hu, hu] at hh
  rw [isoReduction_tensor_smul l E Y n, isoReduction_tensor_smul l E X n]
  let z := unrestrictedTowerTensorSection l E Y n M
    ((proEtaleIsoPostcompose g).op.obj U) 1 x
  have hlin := ((e.hom.app M).val.app U).hom.map_smul (d.hom.app U s)
    (show ((isoReductionFiniteInverse l E g n).obj
      ((scalarReductionExtension l E Y n).obj M)).val.obj U from z)
  change (e.hom.app M).val.app U
    (show ((scalarReductionExtension l E Y n).obj M).val.obj
      ((proEtaleIsoPostcompose g).op.obj U) from
      (inv d).hom.app U (d.hom.app U s) • z) = _ at hlin
  rw [hi] at hlin
  simpa only [z, hh, d, one_smul] using hlin

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isoReduction_moduleTransition
    (e : ∀ n, scalarReductionExtension l E Y n ⋙ isoReductionFiniteInverse l E g n ≅
      isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n)
    (he : ∀ n (M : scalarReductionSource l E Y) (U : X.ProEtᵒᵖ)
      (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
        ((proEtaleIsoPostcompose g).op.obj U))
      (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)),
      ((e n).hom.app M).val.app U
        (unrestrictedTowerTensorSection l E Y n M
          ((proEtaleIsoPostcompose g).op.obj U) a x) =
        unrestrictedTowerTensorSection l E X n ((isoReductionIntegralInverse l E g).obj M) U
          ((isoSectionwiseConstantMap g (CommRingCat.of
            (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app U a) x)
    (M : scalarReductionSource l E Y) (n : ℕ)
    (τY : (scalarReductionRestriction l E Y (n + 1)).obj
        ((scalarReductionExtension l E Y (n + 1)).obj M) ⟶
      (scalarReductionRestriction l E Y n).obj ((scalarReductionExtension l E Y n).obj M))
    (τX : (scalarReductionRestriction l E X (n + 1)).obj
        ((scalarReductionExtension l E X (n + 1)).obj
          ((isoReductionIntegralInverse l E g).obj M)) ⟶
      (scalarReductionRestriction l E X n).obj ((scalarReductionExtension l E X n).obj
        ((isoReductionIntegralInverse l E g).obj M)))
    (hτY : ∀ V b x, τY.val.app V
      (unrestrictedTowerTensorSection l E Y (n + 1) M V b x) =
      unrestrictedTowerTensorSection l E Y n M V
        ((integralCoefficientSheafTransition l E Y n).hom.app V b) x)
    (hτX : ∀ V b x, τX.val.app V
      (unrestrictedTowerTensorSection l E X (n + 1)
        ((isoReductionIntegralInverse l E g).obj M) V b x) =
      unrestrictedTowerTensorSection l E X n ((isoReductionIntegralInverse l E g).obj M) V
        ((integralCoefficientSheafTransition l E X n).hom.app V b) x)
    (U : X.ProEtᵒᵖ)
    (z : ((scalarReductionExtension l E Y (n + 1)).obj M).val.obj
      ((proEtaleIsoPostcompose g).op.obj U)) :
    ((e n).hom.app M).val.app U
      (τY.val.app ((proEtaleIsoPostcompose g).op.obj U) z) =
      τX.val.app U (((e (n + 1)).hom.app M).val.app U z) := by
  classical
  let F := isoReductionIntegralInverse l E g
  choose s hs using isoReduction_restrictionSquare l E g
  let a (m : ℕ) : F.obj ((scalarReductionRestriction l E Y m).obj
      ((scalarReductionExtension l E Y m).obj M)) ≅
      (scalarReductionRestriction l E X m).obj
        ((scalarReductionExtension l E X m).obj (F.obj M)) :=
    (s m).app _ ≪≫ (scalarReductionRestriction l E X m).mapIso ((e m).app M)
  have ha (m : ℕ) (V : X.ProEtᵒᵖ) (x) :
      (a m).hom.val.app V x = ((e m).hom.app M).val.app V x := by
    dsimp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [restrictionMap_apply, hs]
    rfl
  let f := (a (n + 1)).inv ≫ F.map τY ≫
    (a n).hom
  let h := τX
  have eq : f = h := by
    apply SheafOfModules.UnrestrictedTowerProof.identified_hom_ext
      (completedIntegralCommRingProjectionUnrestricted l E X (n + 1)) (F.obj M)
      (scalarReductionExtension l E X (n + 1))
      (isoReduction_extension_obj l E X (n + 1)) _ f h
    intro V b x
    apply Eq.trans (congrArg (f.val.app V)
      (isoReduction_tensorSection_eq l E X (n + 1) (F.obj M) V b x))
    apply Eq.trans _ (congrArg (h.val.app V)
      (isoReduction_tensorSection_eq l E X (n + 1) (F.obj M) V b x)).symm
    let d := isoSectionwiseConstantMap g (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1 + 1))))
    let b' : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj
        ((proEtaleIsoPostcompose g).op.obj V) := (inv d).hom.app V b
    have hb : d.hom.app V b' = b :=
      congrArg (fun f ↦ f.hom.app V b) (IsIso.inv_hom_id d)
    have hp := he (n + 1) M V b' x
    rw [← ha, hb] at hp
    apply Eq.trans (congrArg (f.val.app V) hp.symm)
    apply Eq.trans _ (congrArg (h.val.app V) hp)
    have hinv := moduleIso_hom_inv_apply (a (n + 1)) V
      (unrestrictedTowerTensorSection l E Y (n + 1) M
        ((proEtaleIsoPostcompose g).op.obj V) b' x)
    change (a n).hom.val.app V
      (τY.val.app
        ((proEtaleIsoPostcompose g).op.obj V)
          ((a (n + 1)).inv.val.app V ((a (n + 1)).hom.val.app V _))) = _
    have hy := hτY ((proEtaleIsoPostcompose g).op.obj V) b' x
    have hx := hτX V b x
    have hc := congrArg (fun f ↦ f.hom.app V b')
      (isoReductionConstant_naturality g
        (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l E (n + 1)).comp
            (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))))
    have hcoeff := hc.trans
      (congrArg ((integralCoefficientSheafTransition l E X n).hom.app V) hb)
    apply Eq.trans (congrArg (fun y ↦ (a n).hom.val.app V
      (τY.val.app ((proEtaleIsoPostcompose g).op.obj V) y)) hinv)
    apply Eq.trans (ha n V _)
    apply Eq.trans (congrArg (((e n).hom.app M).val.app V) hy)
    apply Eq.trans (he n M V _ x)
    apply Eq.trans (congrArg (fun c ↦ unrestrictedTowerTensorSection l E X n
      ((isoReductionIntegralInverse l E g).obj M) V c x) hcoeff)
    exact hx.symm.trans (congrArg (h.val.app V) hp).symm
  have hh := congrArg (fun f ↦ (a (n + 1)).hom ≫ f) eq
  simp only [f, ← Category.assoc, Iso.hom_inv_id, Category.id_comp] at hh
  have hh' := congrArg (fun f ↦ f.val.app U z) hh
  change (a n).hom.val.app U _ = h.val.app U ((a (n + 1)).hom.val.app U z)
    at hh'
  simp only [ha] at hh'
  exact hh'

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local semireducible] scalarReductionExtension scalarReductionExistence
  unrestrictedIntegralReductionExistence in
private theorem isoReduction_transition
    (e : ∀ n, scalarReductionExtension l E Y n ⋙ isoReductionFiniteInverse l E g n ≅
      isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n)
    (he : ∀ n (M : scalarReductionSource l E Y) (U : X.ProEtᵒᵖ)
      (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
        ((proEtaleIsoPostcompose g).op.obj U))
      (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)),
      ((e n).hom.app M).val.app U
        (unrestrictedTowerTensorSection l E Y n M
          ((proEtaleIsoPostcompose g).op.obj U) a x) =
        unrestrictedTowerTensorSection l E X n ((isoReductionIntegralInverse l E g).obj M) U
          ((isoSectionwiseConstantMap g (CommRingCat.of
            (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app U a) x)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (z : ((unrestrictedTowerFiniteComplex l E Y (n + 1) P).X i).val.obj
      (op ((proEtaleIsoPostcompose g).obj U))) :
    ((e n).hom.app (P.X i)).val.app (op U)
        (((unrestrictedTowerTransition l E Y P n).f i).val.app
          (op ((proEtaleIsoPostcompose g).obj U)) z) =
      (((unrestrictedTowerTransition l E X
        ((isoReductionIntegralComplex l E g).obj P) n).f i).val.app (op U))
          (((e (n + 1)).hom.app (P.X i)).val.app (op U) z) := by
  apply isoReduction_moduleTransition l E g e he (P.X i) n
    ((unrestrictedTowerTransition l E Y P n).f i)
    ((unrestrictedTowerTransition l E X ((isoReductionIntegralComplex l E g).obj P) n).f i)
  · intro V b x
    unfold unrestrictedTowerTransition unrestrictedIntegralTransition
      unrestrictedTowerTensorSection
    exact (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec P i V b x
  · intro V b x
    unfold unrestrictedTowerTransition unrestrictedIntegralTransition
      unrestrictedTowerTensorSection
    exact (unrestrictedIntegralTransition_existsUnique l E X n).exists.choose_spec
      ((isoReductionIntegralComplex l E g).obj P) i V b x

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private noncomputable def isoReduction_complexSquare (n : ℕ)
    (e : scalarReductionExtension l E Y n ⋙ isoReductionFiniteInverse l E g n ≅
      isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n) :
    (scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ) ⋙
        isoReductionFiniteComplex l E g n ≅
      isoReductionIntegralComplex l E g ⋙
        (scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n))
      (.up ℤ)).symm

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem isoReduction_complexSquare_component (n : ℕ)
    (e : scalarReductionExtension l E Y n ⋙ isoReductionFiniteInverse l E g n ≅
      isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (i : ℤ) :
    ((isoReduction_complexSquare l E g n e).hom.app P).f i = e.hom.app (P.X i) := by
  change e.hom.app (P.X i) ≫ 𝟙 _ = e.hom.app (P.X i)
  exact Category.comp_id _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private noncomputable def isoReduction_counit_pointwise (W : Scheme.{t}) (n : ℕ) :
    (Functor.RightExtension.mk (scalarReductionDerivedExtension l E W n)
      (towerCounit l E W n)).IsPointwiseRightKanExtension := by
  let A := scalarReductionSource l E W
  let B := scalarReductionTarget l E W n
  let L := scalarReductionExtension l E W n
  let T := scalarReductionDerivedExtension l E W n
  let ε := scalarReductionCounit l E W n
  let F := L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let : F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) :=
    by
      simpa only [F, L, scalarReductionExtension] using
        (scalarReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose_spec.2.1
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) :=
    by
      unfold T ε scalarReductionCounit scalarReductionDerivedExtension
      exact (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.1
  let q := HomotopyCategory.quotient A (.up ℤ)
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh F T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (L.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  have hβ := pointwise_change_iso T i j α hα
  convert hβ using 1
  simp only [towerCounit, α, i, j, A, B, L, T, ε, q, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Category.assoc]

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem isoReduction_finiteComparison_formula (W : Scheme.{t}) (n : ℕ)
    {P P' K : CochainComplex (scalarReductionSource l E W) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) q') :
    letI : QuasiIso q' := hq'.1
    letI := towerCounit_isIso l E W n P hq.2
    (unrestrictedTowerFiniteComparison l E W n q q' hq hq').hom =
      inv ((towerCounit l E W n).app P) ≫
        (scalarReductionDerivedExtension l E W n).map (DerivedCategory.Q.map q) ≫
        inv ((scalarReductionDerivedExtension l E W n).map (DerivedCategory.Q.map q')) ≫
        (towerCounit l E W n).app P' := by
  let : QuasiIso q := hq.1
  let : QuasiIso q' := hq'.1
  let := towerCounit_isIso l E W n P hq.2
  let := towerCounit_isIso l E W n P' hq'.2
  let a := (scalarReductionDerivedExtension l E W n).map (DerivedCategory.Q.map q)
  let b := (scalarReductionDerivedExtension l E W n).map (DerivedCategory.Q.map q')
  let c := unrestrictedTowerResolutionIso l E W n q hq
  let d := unrestrictedTowerResolutionIso l E W n q' hq'
  have hc : a ≫ c.hom = (towerCounit l E W n).app P :=
    towerResolution_hom l E W n q hq
  have hd : b ≫ d.hom = (towerCounit l E W n).app P' :=
    towerResolution_hom l E W n q' hq'
  change c.inv ≫ d.hom = _
  apply (cancel_epi ((towerCounit l E W n).app P)).1
  simp only [IsIso.hom_inv_id_assoc]
  calc
    _ = (a ≫ c.hom) ≫ c.inv ≫ d.hom := by rw [hc]
    _ = a ≫ d.hom := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      exact (congrArg (a ≫ ·) ((IsIso.inv_comp_eq b).2 hd.symm)).symm

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The K-flat and flat-term conditions of the statement, with independent sizes.
Source: Stacks Tags 06YN, 03ER
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
def IsoReductionFlatComplex (W : Scheme.{t})
    (P : CochainComplex (scalarReductionSource l E W) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The finite derived inverse image, expressed on represented complexes.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
def isoReductionFiniteDerived (n : ℕ) :
    DerivedCategory (scalarReductionTarget l E Y n) ⥤
      DerivedCategory (scalarReductionTarget l E X n) :=
  (isoReductionFiniteInverse l E g n).mapDerivedCategory

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The image of the canonical resolution comparison, expressed at the termwise
inverse-image complexes using the canonical localization factorization.
Source: Stacks Tags 015F, 06YY
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower). -/
def isoReductionImageComparison (n : ℕ)
    {P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q') :=
  ((isoReductionFiniteInverse l E g n).mapDerivedCategoryFactors.app _).symm ≪≫
    (isoReductionFiniteDerived l E g n).mapIso
      (unrestrictedTowerFiniteComparison l E Y n q q' hq hq') ≪≫
    (isoReductionFiniteInverse l E g n).mapDerivedCategoryFactors.app _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Exact relabelling preserves the quasi-isomorphism of an augmentation.
Source: Stacks Tag 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower).
Proof: the recorded inverse image is additive and exact. It commutes with cohomology
by preserving kernels and cokernels. Therefore a cohomology isomorphism remains
an isomorphism in every degree. -/
theorem isoReductionMapQuasiIso
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (hq : QuasiIso q) :
    QuasiIso ((isoReductionIntegralComplex l E g).map q) := by
  have : QuasiIso q := hq
  exact HomologicalComplex.quasiIso_map_of_preservesHomology q
    (isoReductionIntegralInverse l E g)

attribute [local irreducible] isoReductionFiniteDerived isoReductionImageComparison
attribute [local irreducible] Functor.mapDerivedCategory
  towerCounit unrestrictedTowerResolutionIso
  unrestrictedTowerFiniteComparison

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isoReduction_derivedComparison
    (n : ℕ)
    (e : scalarReductionExtension l E Y n ⋙ isoReductionFiniteInverse l E g n ≅
      isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n)
    {P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (hP : IsoReductionFlatComplex l E Y P) (hP' : IsoReductionFlatComplex l E Y P')
    (q : P ⟶ K) (q' : P' ⟶ K) (hq : QuasiIso q) (hq' : QuasiIso q')
    (hFP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      ((isoReductionIntegralComplex l E g).obj P))
    (hFP' : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      ((isoReductionIntegralComplex l E g).obj P')) :
    (isoReductionImageComparison l E g n q q' ⟨hq, hP.1⟩ ⟨hq', hP'.1⟩).hom ≫
        DerivedCategory.Q.map ((isoReduction_complexSquare l E g n e).app P').hom =
      DerivedCategory.Q.map ((isoReduction_complexSquare l E g n e).app P).hom ≫
        (unrestrictedTowerFiniteComparison l E X n
          ((isoReductionIntegralComplex l E g).map q)
          ((isoReductionIntegralComplex l E g).map q')
          ⟨isoReductionMapQuasiIso l E g q hq, hFP⟩
          ⟨isoReductionMapQuasiIso l E g q' hq', hFP'⟩).hom := by
  let F := isoReductionIntegralInverse l E g
  let G := isoReductionFiniteInverse l E g n
  let FY := (scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)
  let FX := (scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)
  let β := isoReduction_complexSquare l E g n e
  let j : (FY ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ (FX ⋙ DerivedCategory.Q) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft FY G.mapDerivedCategoryFactors ≪≫
      (Functor.associator FY (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q).symm ≪≫
      Functor.isoWhiskerRight β DerivedCategory.Q ≪≫
      Functor.associator (F.mapHomologicalComplex (.up ℤ)) FX DerivedCategory.Q
  let : G.IsEquivalence := isoReduction_equivalence.{t, u} g
    (isoSectionwiseConstantMap g (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
  let : G.mapDerivedCategory.IsEquivalence := inferInstance
  let : G.mapDerivedCategory.PreservesPointwiseRightKanExtension
      (FY ⋙ DerivedCategory.Q) DerivedCategory.Q :=
    pointwisePostcomposeEquivalence G.mapDerivedCategory _ _
  have hpost := (isoReduction_counit_pointwise l E Y n).postcompose G.mapDerivedCategory
  have huniv := Functor.RightExtension.isPointwiseRightKanExtensionEquivOfIso
    (Functor.RightExtension.postcompose₂ObjMkIso G.mapDerivedCategory
      (towerCounit l E Y n)) hpost
  let : (scalarReductionDerivedExtension l E Y n ⋙ G.mapDerivedCategory).IsRightKanExtension
      ((Functor.associator DerivedCategory.Q (scalarReductionDerivedExtension l E Y n)
        G.mapDerivedCategory).inv ≫ Functor.whiskerRight (towerCounit l E Y n)
          G.mapDerivedCategory) := huniv.isRightKanExtension
  let : QuasiIso q := hq
  let : QuasiIso q' := hq'
  let : QuasiIso ((isoReductionIntegralComplex l E g).map q) :=
    isoReductionMapQuasiIso l E g q hq
  let : QuasiIso ((isoReductionIntegralComplex l E g).map q') :=
    isoReductionMapQuasiIso l E g q' hq'
  let cP := towerCounit_isIso l E Y n P hP.1
  let cP' := towerCounit_isIso l E Y n P' hP'.1
  let cFP := towerCounit_isIso l E X n ((isoReductionIntegralComplex l E g).obj P) hFP
  let cFP' := towerCounit_isIso l E X n ((isoReductionIntegralComplex l E g).obj P') hFP'
  have hy := isoReduction_finiteComparison_formula l E Y n q q' ⟨hq, hP.1⟩ ⟨hq', hP'.1⟩
  have hx := isoReduction_finiteComparison_formula l E X n _ _
    ⟨isoReductionMapQuasiIso l E g q hq, hFP⟩
    ⟨isoReductionMapQuasiIso l E g q' hq', hFP'⟩
  have hh := comparisonOfUniversalWithFormulas DerivedCategory.Q DerivedCategory.Q
    (F.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategory G.mapDerivedCategory
    (FY ⋙ DerivedCategory.Q) (FX ⋙ DerivedCategory.Q)
    (scalarReductionDerivedExtension l E Y n) (scalarReductionDerivedExtension l E X n)
    (towerCounit l E Y n) (towerCounit l E X n) F.mapDerivedCategoryFactors.symm j q q'
    (_hQq := (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq)
    (hQq' := (DerivedCategory.isIso_Q_map_iff_quasiIso _ q').2 hq')
    (_hFq := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (isoReductionMapQuasiIso l E g q hq))
    (hFq' := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (isoReductionMapQuasiIso l E g q' hq'))
    (hεP := cP) (_hεP' := cP') (hεFP := cFP) (_hεFP' := cFP')
    (unrestrictedTowerFiniteComparison l E Y n q q' ⟨hq, hP.1⟩ ⟨hq', hP'.1⟩).hom
    (unrestrictedTowerFiniteComparison l E X n
      ((isoReductionIntegralComplex l E g).map q)
      ((isoReductionIntegralComplex l E g).map q')
      ⟨isoReductionMapQuasiIso l E g q hq, hFP⟩
      ⟨isoReductionMapQuasiIso l E g q' hq', hFP'⟩).hom
    hy hx
  have hj (A : CochainComplex (scalarReductionSource l E Y) ℤ) :
      j.hom.app A = G.mapDerivedCategoryFactors.hom.app (FY.obj A) ≫
        DerivedCategory.Q.map (β.hom.app A) := by
    dsimp only [j, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp]
    exact congrArg (G.mapDerivedCategoryFactors.hom.app (FY.obj A) ≫ ·)
      (Category.comp_id (DerivedCategory.Q.map (β.hom.app A)))
  unfold isoReductionImageComparison isoReductionFiniteDerived
  exact conjugatedComparison
    (G.mapDerivedCategoryFactors.app (FY.obj P))
    (G.mapDerivedCategoryFactors.app (FY.obj P')) _ _ _ _ _ _ (hj P) (hj P') hh

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized tensor identifications intertwine quotient arrows, transitions,
chain maps and the canonical finite-coefficient resolution comparisons.
Source: blueprint main-20261015, ordinary compact cohomology, coefficient paragraph;
Stacks Tags 03EL, 03EK, 06YS, 06YY and 015F
(blueprint: lem-weil-isomorphism-derived-pullback-reduction-tower).
Proof:
1. Inverse image preserves the completed coefficient limit. Naturality of the finite
constant comparisons makes their inverse limit a ring isomorphism with the stated
projection squares (lem-weil-proetale-isomorphism-inverse-image).
2. Apply lem-pur-isomorphism-inverse-image-tensor-hom degreewise, then transport
coefficients along those ring isomorphisms. The projection square verifies the
balanced relation; the inverse uses the inverse coefficient isomorphisms.
3. The coefficient factor has degree zero. Tensor naturality for d_P makes these
maps and their inverses chain maps (def-pc-tensor-complex-sheaves).
4. The local formula sends x tensor 1 to F(x) tensor 1 because c is unital.
This is precisely the quotient-arrow equation (def-weil-integral-reduction-tower).
5. Naturality of c for coefficient reductions identifies the two transition maps
on pure tensors. Tensor generation and sheafification extend this to all sections.
6. Tensor naturality in P gives the displayed chain-map naturality equation.
7. Exact inverse image preserves quasi-isomorphisms and homotopies by
situation-conventions, so it descends to derived categories.
8. Apply lem-pur-quasi-isos-saturated-triangulated to find a common roof for q,q'.
Resolve its source by lem-pc-kflat-resolution. Pullback preserves K-flatness and
flat terms by lem-weil-pbc-ringed-pullback-preserves-kflat; scalar-isomorphism
normalization identifies it with inverse image (lem-weil-sheaf-scalar-extension-ring-iso).
9. The universal derived-change-of-rings counit identifies theta with
[a_n] inverse followed by [b_n], using lem-pur-derived-change-of-rings and
lem-pur-left-derived-from-kflat-class. These are exactly the comparisons of
lem-weil-integral-reduction-tower-well-defined on both schemes.
10. Apply chain-map naturality to a,b and cancel the invertible reductions of a.
This yields the final equality in the finite-coefficient derived category on X. -/
theorem isomorphismReductionTower
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      IsoReductionFlatComplex l E Y P → ∀ n : ℕ,
        (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
          unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P),
      (∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : IsoReductionFlatComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
        (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
        (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (((β P hP n).hom.f i).val.app (op U))
          (unrestrictedTowerTensorSection l E Y n (P.X i)
            (op ((proEtaleIsoPostcompose g).obj U)) a x) =
          unrestrictedTowerTensorSection l E X n
            (((isoReductionIntegralComplex l E g).obj P).X i) (op U)
            ((isoSectionwiseConstantMap g (CommRingCat.of
              (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
                (op U) a) x) ∧
      (∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : IsoReductionFlatComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
        (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (((β P hP n).hom.f i).val.app (op U))
          (((unrestrictedTowerUnit l E Y P n).f i).val.app
            (op ((proEtaleIsoPostcompose g).obj U)) x) =
          (((unrestrictedTowerUnit l E X ((isoReductionIntegralComplex l E g).obj P) n).f i).val.app
             (op U)) x) ∧
      (∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : IsoReductionFlatComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
        (z : ((unrestrictedTowerFiniteComplex l E Y (n + 1) P).X i).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (((β P hP n).hom.f i).val.app (op U))
          (((unrestrictedTowerTransition l E Y P n).f i).val.app
            (op ((proEtaleIsoPostcompose g).obj U)) z) =
          (((unrestrictedTowerTransition l E X
            ((isoReductionIntegralComplex l E g).obj P) n).f i).val.app (op U))
              ((((β P hP (n + 1)).hom.f i).val.app (op U)) z)) ∧
      (∀ (P P' : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : IsoReductionFlatComplex l E Y P) (hP' : IsoReductionFlatComplex l E Y P')
        (a : P ⟶ P') (n : ℕ),
        (isoReductionFiniteComplex l E g n).map
            (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).map a) ≫
          (β P' hP' n).hom =
        (β P hP n).hom ≫
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).map
            ((isoReductionIntegralComplex l E g).map a)) ∧
      (∀ (P P' K : CochainComplex (scalarReductionSource l E Y) ℤ)
        (hP : IsoReductionFlatComplex l E Y P) (hP' : IsoReductionFlatComplex l E Y P')
        (q : P ⟶ K) (q' : P' ⟶ K) (hq : QuasiIso q) (hq' : QuasiIso q')
        (hFP : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E X)
          ((isoReductionIntegralComplex l E g).obj P))
        (hFP' : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E X)
          ((isoReductionIntegralComplex l E g).obj P')) (n : ℕ),
        (isoReductionImageComparison l E g n q q' ⟨hq, hP.1⟩ ⟨hq', hP'.1⟩).hom ≫
          DerivedCategory.Q.map (β P' hP' n).hom =
        DerivedCategory.Q.map (β P hP n).hom ≫
          (unrestrictedTowerFiniteComparison l E X n
            ((isoReductionIntegralComplex l E g).map q)
            ((isoReductionIntegralComplex l E g).map q')
            ⟨isoReductionMapQuasiIso l E g q hq, hFP⟩
            ⟨isoReductionMapQuasiIso l E g q' hq', hFP'⟩).hom) := by
  classical
  let e := fun n ↦ (isoReduction_tensorSquare l E g n).choose
  have he0 := fun n ↦ (isoReduction_tensorSquare l E g n).choose_spec
  have he := fun n ↦ isoReduction_tensorUnit l E g n (e n) (he0 n)
  let β := fun (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) ↦
    (isoReduction_complexSquare l E g n (e n)).app P
  have hb (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) (i : ℤ) :
      (β P n).hom.f i = (e n).hom.app (P.X i) :=
    isoReduction_complexSquare_component l E g n (e n) P i
  have ht := fun n ↦ isoReduction_tensorFormula l E g n (e n) (he n)
  refine ⟨fun P _ n ↦ β P n, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP n i U a x
    change ((β P n).hom.f i).val.app (op U) _ = _
    rw [hb]
    exact ht n (P.X i) (op U) a x
  · intro P hP n i U x
    change ((β P n).hom.f i).val.app (op U) _ = _
    rw [hb]
    have huY := unrestrictedTowerUnit_condition l E Y P n i
      (op ((proEtaleIsoPostcompose g).obj U)) x
    have huX := unrestrictedTowerUnit_condition l E X
      ((isoReductionIntegralComplex l E g).obj P) n i (op U) x
    rw [huY, huX]
    have hx := ht n (P.X i) (op U) 1 x
    have h1 : (isoSectionwiseConstantMap g (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app (op U) 1 =
        (1 : (integralCoefficientCommRingSheaf l E X n).obj.obj (op U)) :=
      map_one _
    rw [h1] at hx
    exact hx
  · intro P hP n i U z
    rw [hb, hb]
    exact isoReduction_transition l E g e ht P n i U z
  · intro P P' hP hP' a n
    exact (isoReduction_complexSquare l E g n (e n)).hom.naturality a
  · intro P P' K hP hP' q q' hq hq' hFP hFP' n
    exact isoReduction_derivedComparison l E g n (e n) hP hP' q q' hq hq' hFP hFP'

end WeilConjectures
