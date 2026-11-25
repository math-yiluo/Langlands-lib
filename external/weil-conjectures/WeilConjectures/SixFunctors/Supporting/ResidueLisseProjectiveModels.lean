/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SixFunctors.Integral.IntegralDerivedReductionSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicGeometry.Cover.Open

import WeilConjectures.SixFunctors.Supporting.CompleteTopResidueCellCone
import WeilConjectures.SixFunctors.Supporting.ResidueLisseClopenBases
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Projective models from lisse residue cohomology

Source: Stacks Project, proetale.tex, Tag 09C3 (blueprint:
lem-fix-residue-lisse-projective-models).

The conclusion records a finite disjoint open cover and, on every member, a bounded
complex whose terms split off finite sums of the completed coefficient sheaf.  The
differentials are unrestricted sheaf-linear maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open CochainComplex Opposite
open AlgebraicGeometry.Scheme

namespace WeilConjectures

-- This is the cone argument over an arbitrary abelian category; in particular it
-- works on the original pro-etale site, whose object and morphism sizes differ.
private theorem attachCell {A : Type v} [Category.{w} A] [Abelian A]
    [HasDerivedCategory A] (a b : ℤ) (hab : a ≤ b) (P : A) (M : DerivedCategory A)
    (K : CochainComplex A ℤ)
    (hsupp : ∀ q : ℤ, q < a ∨ b - 1 < q → IsZero (K.X q))
    (hproj : ∀ q : ℤ, Projective (K.X q))
    (v₁ : DerivedCategory.Q.obj ((singleFunctor A b).obj P) ⟶ M)
    (v₂ : M ⟶ DerivedCategory.Q.obj K)
    (δ : DerivedCategory.Q.obj K ⟶
      (DerivedCategory.Q.obj ((singleFunctor A b).obj P))⟦1⟧)
    (htri : Triangle.mk v₁ v₂ δ ∈ distTriang (DerivedCategory A)) :
    ∃ D : CochainComplex A ℤ, Nonempty (DerivedCategory.Q.obj D ≅ M) ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero (D.X q)) ∧
      (∀ q : ℤ, q ≠ b → Nonempty (D.X q ≅ K.X q)) ∧ Nonempty (D.X b ≅ P) := by
  let T := (singleFunctor A (b - 1)).obj P
  let s := (((singleFunctors A).postcomp DerivedCategory.Q).shiftIso
    1 (b - 1) b (by omega)).app P
  let : ∀ q : ℤ, Projective (K.X q) := hproj
  let : K.IsStrictlyLE (b - 1) :=
    (isStrictlyLE_iff _ _).2 (fun q hq ↦ hsupp q (Or.inr hq))
  let : K.IsKProjective := isKProjective_of_projective K (b - 1)
  obtain ⟨gh, hgh⟩ := (IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient A (.up ℤ)).obj T)).surjective
      ((DerivedCategory.quotientCompQhIso A).hom.app K ≫ δ ≫ s.hom ≫
        (DerivedCategory.quotientCompQhIso A).inv.app T)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective gh
  have hg : DerivedCategory.Q.map g ≫ s.inv = δ := by
    have hh : DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map g) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app T =
        (DerivedCategory.quotientCompQhIso A).hom.app K ≫ DerivedCategory.Q.map g :=
      DerivedCategory.quotientCompQhIso_hom_naturality g
    apply (cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app K)).mp
    rw [← Category.assoc, ← hh, hgh]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id, Category.comp_id]
  let D := (mappingCone g)⟦(-1 : ℤ)⟧
  have hDM : Nonempty (DerivedCategory.Q.obj D ≅ M) := by
    let Tc := DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle g)
    let Tr := (Triangle.mk v₁ v₂ δ).rotate.rotate
    let e := isoTriangleOfIso₁₂ Tc Tr (DerivedCategory.mappingCone_triangle_distinguished g)
      (rot_of_distTriang _ (rot_of_distTriang _ htri)) (Iso.refl _) s.symm (by
        change DerivedCategory.Q.map g ≫ s.inv = 𝟙 _ ≫ δ
        simpa only [Category.id_comp] using hg)
    exact ⟨(DerivedCategory.Q.commShiftIso (-1)).app (mappingCone g) ≪≫
      (CategoryTheory.shiftFunctor _ (-1)).mapIso (Triangle.π₃.mapIso e) ≪≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app M⟩
  refine ⟨D, hDM, ?_, ?_, ?_⟩
  · intro q hq
    apply (shiftFunctorObjXIso (mappingCone g) (-1) q (q - 1) rfl).isZero_iff.mpr
    apply (mappingCone.isZero_X_iff g (q - 1)).2
    constructor
    · convert hsupp q (by omega) using 1
      congr 1
      omega
    · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) (b - 1) P (q - 1) (by omega)
  · intro q hq
    exact ⟨shiftFunctorObjXIso (mappingCone g) (-1) q (q - 1) rfl ≪≫
      { hom := (mappingCone.fst g).1.v (q - 1) q (by omega)
        inv := (mappingCone.inl g).v q (q - 1) (by omega)
        hom_inv_id := by
          apply mappingCone.ext_to g (q - 1) q (by omega)
          · simp
          · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ)
              (b - 1) P (q - 1) (by omega)).eq_of_tgt _ _
        inv_hom_id := by simp }⟩
  · exact ⟨shiftFunctorObjXIso (mappingCone g) (-1) b (b - 1) rfl ≪≫
      { hom := (mappingCone.snd g).v (b - 1) (b - 1) (add_zero _)
        inv := (mappingCone.inr g).f (b - 1)
        hom_inv_id := by
          apply mappingCone.ext_to g (b - 1) b (by omega)
          · exact (hsupp b (Or.inr (by omega))).eq_of_tgt _ _
          · simp
        inv_hom_id := by simp } ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) (b - 1) P⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private noncomputable def finiteFreeProductIso (X : Scheme.{u}) (n : ℕ) :
    topCellIntegralFree.{u} l E X n ≅
      ∏ᶜ fun _ : Fin n ↦ (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) :
          scalarReductionSource.{u, u} l E X) :=
  by
    let := integralCoefficientAbSheafify.{u, u} X
    let := integralCoefficientAbLocallyBijective.{u, u} X
    let F : Fin n → scalarReductionSource.{u, u} l E X := fun _ ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
    letI : HasBiproduct F := HasBiproduct.of_hasProduct F
    change (∐ fun _ : ULift.{u + 1} (Fin n) ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)) ≅ _
    exact Sigma.whiskerEquiv (f := fun _ : ULift.{u + 1} (Fin n) ↦
          SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)) (g := F)
        (Equiv.ulift : ULift.{u + 1} (Fin n) ≃ Fin n) (fun _ ↦ Iso.refl _) ≪≫
      (biproduct.isoCoproduct F).symm ≪≫ biproduct.isoProduct F

private theorem freeZero (X : Scheme.{u}) : IsZero (topCellIntegralFree.{u} l E X 0) := by
  let := integralCoefficientAbSheafify.{u, u} X
  let := integralCoefficientAbLocallyBijective.{u, u} X
  apply (IsZero.iff_id_eq_zero
    (C := scalarReductionSource.{u, u} l E X) (topCellIntegralFree.{u} l E X 0)).mpr
  apply Cofan.IsColimit.hom_ext
    (@SheafOfModules.isColimitFreeCofan X.ProEt inferInstance (ProEt.topology X)
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
      (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
      (integralCoefficientAbLocallyBijective.{u, u} X) (ULift.{u + 1} (Fin 0)))
  intro i
  exact Fin.elim0 i.down

private theorem singleFree (X : Scheme.{u}) (b : ℤ) (r : ℕ) (q : ℤ) :
    ∃ n : ℕ, Nonempty
      (((CochainComplex.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (topCellIntegralFree.{u} l E X r)).X q ≅ topCellIntegralFree.{u} l E X n) := by
  by_cases h : q = b
  · subst q
    exact ⟨r, ⟨HomologicalComplex.singleObjXSelf (.up ℤ) b _⟩⟩
  · exact ⟨0, ⟨(HomologicalComplex.isZero_single_obj_X (.up ℤ) b _ q h).isoZero ≪≫
      (freeZero l E X).isoZero.symm⟩⟩

-- Induction takes place on one fixed component with fixed residue bases. No
-- constructibility hypothesis is needed once this data has been supplied.
private theorem localFreeModel (X : Scheme.{u}) [CompactSpace X]
    (hweak : ∀ (F G : Sheaf (ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 X)))))
    (hproj : ∀ n : ℕ, Projective (topCellIntegralFree.{u} l E X n))
    (M : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X M)
    (a b : ℤ) (hab : a ≤ b) (r : ℤ → ℕ)
    (theta : ∀ q : Set.Icc a b, topCellResidueFree.{u} l E X (r q.val) ≅
      (DerivedCategory.homologyFunctor (scalarReductionTarget.{u, u} l E X 0) q.val).obj
        ((scalarReductionDerivedExtension.{u, u} l E X 0).obj M))
    (hTor : ∀ V : X.ProEt,
      HasProEtaleTorAmplitude V.left (Padic.coefficientExtensionRing l E 1)
        ((proEtaleRingDerivedPullback V.hom
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
          (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
          ((scalarReductionDerivedExtension.{u, u} l E X 0).obj M)) a b) :
    ∃ P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ,
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ q : ℤ, ∃ n : ℕ, Nonempty (P.X q ≅ topCellIntegralFree.{u} l E X n)) ∧
      Nonempty (M ≅ DerivedCategory.Q.obj P) := by
  classical
  generalize hd : (b - a).toNat = d
  induction d using Nat.strong_induction_on generalizing M b with
  | h d ih =>
    obtain ⟨e, f, L, g, delta, _he, htri, hL, _hf, _hsplit, _hcone,
      _hcontract, _hhomotopy, _hresidue, hthetaL, hTorL, hbase, _hrank⟩ :=
      complete_top_residue_cell_cone l E X hweak M hcomplete a b hab r theta hTor
    by_cases heq : a = b
    · have : IsIso f := (hbase heq).2.2
      let P := (singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (topCellIntegralFree.{u} l E X (r b))
      refine ⟨P, ?_, inferInstance, singleFree l E X b (r b), ⟨(asIso f).symm⟩⟩
      simpa only [heq] using (inferInstance : P.IsStrictlyGE b)
    · have hlt : a < b := lt_of_le_of_ne hab heq
      obtain ⟨Q, hQge, hQle, hQfree, ⟨eQ⟩⟩ :=
        ih (b - 1 - a).toNat (by omega) L hL (b - 1) (by omega)
          (fun q ↦ Classical.choice (hthetaL q)) (hTorL hlt) rfl
      have hQsupp : ∀ q : ℤ, q < a ∨ b - 1 < q → IsZero (Q.X q) := by
        intro q hq
        rcases hq with hq | hq
        · exact (isStrictlyGE_iff Q a).mp hQge q hq
        · exact (isStrictlyLE_iff Q (b - 1)).mp hQle q hq
      have hQproj : ∀ q : ℤ, Projective (Q.X q) := by
        intro q
        obtain ⟨n, ⟨en⟩⟩ := hQfree q
        exact Projective.of_iso en.symm (hproj n)
      have htriQ : Triangle.mk f (g ≫ eQ.hom) (eQ.inv ≫ delta) ∈
          distTriang (DerivedCategory (scalarReductionSource.{u, u} l E X)) := by
        exact (distinguished_iff_of_iso
          (Triangle.isoMk (Triangle.mk f g delta)
            (Triangle.mk f (g ≫ eQ.hom) (eQ.inv ≫ delta))
            (Iso.refl _) (Iso.refl _) eQ (by simp) (by simp) (by simp))).mp htri
      obtain ⟨P, ⟨eP⟩, hsupp, hlow, ⟨htop⟩⟩ :=
        attachCell a b hab (topCellIntegralFree.{u} l E X (r b)) M Q hQsupp hQproj
          f (g ≫ eQ.hom) (eQ.inv ≫ delta) htriQ
      refine ⟨P, (isStrictlyGE_iff P a).mpr (fun q hq ↦ hsupp q (Or.inl hq)),
        (isStrictlyLE_iff P b).mpr (fun q hq ↦ hsupp q (Or.inr hq)), ?_, ⟨eP.symm⟩⟩
      intro q
      by_cases hq : q = b
      · subst q
        exact ⟨r b, ⟨htop⟩⟩
      · obtain ⟨n, ⟨en⟩⟩ := hQfree q
        exact ⟨n, ⟨(Classical.choice (hlow q hq)) ≪≫ en⟩⟩

/- The finite family is indexed by `Fin n`; `n = 0` therefore covers the empty
scheme, while the pairwise disjointness condition retains the stated clopen case. -/
/-- A complete integral complex with bounded finite locally constant residue cohomology
and finite residue Tor amplitude has bounded finite-projective sheaf models on a finite
clopen partition. Differentials are arbitrary maps over the completed ring sheaf.

Source: Stacks Project, proetale.tex, Tag 09C3, with Lambda = O_E and I = (varpi);
algebraization.tex, Tag 099I identifies the complete coefficient categories
(blueprint: lem-fix-residue-lisse-projective-models).

Proof, following the six steps of the node:
1. lem-sf-residue-lisse-clopen-bases gives a finite disjoint open cover. On each member X
   the completed pullback M of K is complete, X is compact and weakly contractible, the
   completed finite free sheaves are projective, and one interval [a,b] with ranks r
   identifies the residue cohomology with finite free residue sheaves; the residue Tor
   interval [a,b] holds on every object of the pro-etale site of X.
2. On X induct strongly on (b-a).toNat. lem-sf-complete-top-residue-cell-cone gives a
   distinguished triangle F[-b] -> M -> L -> F[-b+1] with F = B_X^(r b), L complete,
   and the shortened residue bases and Tor interval [a,b-1].
3. If a = b the first map is an isomorphism, and the single complex F in degree b is
   the model; its other terms are zero, the free sheaf on the empty basis.
4. If a < b, induction gives a finite free model Q of L in [a,b-1]; its terms are
   projective, and the triangle is transported along L = Q(Q).
5. `attachCell`: Q is a bounded-above complex of projectives, hence K-projective, so
   the connecting map is a chain map g : Q -> F[-b+1]; comparing the twice-rotated
   triangle with the cone triangle of g gives Q(Cone(g)[-1]) = M, with terms Q^q for
   q != b and F in degree b.
6. A finite free sheaf is the finite product of copies of B_X through the finite
   biproduct comparisons; the term isomorphisms give inclusion and retraction. The
   empty cover handles the empty scheme; differentials stay arbitrary. -/
theorem residue_lisse_projective_models
    (S : Scheme.{u}) (hS : IsAffine S)
    (hweak : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1}
      (Scheme.ProEt.mk (𝟙 S)))
    (K : DerivedCategory (integralTowerModules.{u, u} l E S))
    (hcomplete : IsDerivedCompleteUnrestricted l E S K)
    (hresidue : intrinsicFiniteTorsionConstructible l E 1 (by omega) S
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K))
    (hlisse : ∀ q : ℤ, IsLocallyConstantProEtaleModuleSheaf S
      (Padic.coefficientExtensionRing l E 1)
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules S (proEtaleConstantRing S
          (Padic.coefficientExtensionRing l E 1))) q).obj
        ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K)))
    (hTor : HasFiniteProEtaleTorAmplitude S
      (Padic.coefficientExtensionRing l E 1)
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K)) :
    ∃ (n : ℕ) (U : Fin n → S.Opens),
      (⨆ i, U i) = ⊤ ∧
      Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
      ∀ i : Fin n,
        ∃ (P : CochainComplex (integralTowerModules.{u, u} l E (U i).toScheme) ℤ)
          (a b : ℤ),
          a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ r : ℤ, ∃ (N : ℕ)
            (ι : P.X r ⟶ ∏ᶜ fun _ : Fin N ↦
              SheafOfModules.unit
                (completedIntegralCoefficientSheafUnrestricted l E (U i).toScheme))
            (ρ : (∏ᶜ fun _ : Fin N ↦
              SheafOfModules.unit
                (completedIntegralCoefficientSheafUnrestricted l E (U i).toScheme))
              ⟶ P.X r),
            ι ≫ ρ = 𝟙 _) ∧
          Nonempty
            ((integralDerivedPullback l E (U i).ι).obj K ≅
              DerivedCategory.Q.obj P) := by
  classical
  obtain ⟨n, U, hcover, hdisjoint, hlocal⟩ :=
    residue_lisse_clopen_bases l E S hS hweak K hcomplete hresidue hlisse hTor
  refine ⟨n, U, hcover, hdisjoint, fun i ↦ ?_⟩
  obtain ⟨hcompact, hweakU, hprojective, hcompleteU, a, b, r, hab, htheta, hTorU⟩ :=
    hlocal i
  let := hcompact
  obtain ⟨P, hge, hle, hfree, hP⟩ := localFreeModel l E (U i).toScheme hweakU
    hprojective _ hcompleteU a b hab r (fun q ↦ Classical.choice (htheta q)) hTorU
  refine ⟨P, a, b, hab, hge, hle, ?_, hP⟩
  intro q
  obtain ⟨N, ⟨e⟩⟩ := hfree q
  let e' := e ≪≫ finiteFreeProductIso l E (U i).toScheme N
  exact ⟨N, e'.hom, e'.inv, e'.hom_inv_id⟩

end WeilConjectures
