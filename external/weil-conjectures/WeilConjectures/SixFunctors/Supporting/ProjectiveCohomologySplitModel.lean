/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Finite free cohomology and projective split models

Source: Stacks Project, proetale.tex, Tag 09C3, generator lifting in the proof of
lemma-local-structure-constructible-complex; derived.tex, Tag 064B
(blueprint: lem-sf-projective-cohomology-split-model).

The zero-differential model and its summand inclusions are explicit constructions.
The cohomology map and its generator-section map use the canonical single-complex
and localization comparisons, so the asserted bijection has a specified forward map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ZeroObject

namespace WeilConjectures

variable {U : Scheme.{u}}
    (C : Sheaf (Scheme.ProEt.topology U) CommRingCat.{max (u + 1) v})

/-- The coefficient ring sheaf, forgetting only commutativity.
Source: Stacks 09C3, module sheaves over the coefficient sheaf
(blueprint: lem-sf-projective-cohomology-split-model). -/
def sfSplitRings : Sheaf (Scheme.ProEt.topology U) RingCat.{max (u + 1) v} :=
  (sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})).obj C

/-- The prescribed zero-differential complex: finite free terms in `[a,b]`, zero elsewhere.
Source: Stacks 09C3, simultaneous generator lifting in the proof
(blueprint: lem-sf-projective-cohomology-split-model). -/
def sfSplitComplex (a b : ℤ) (r : ℤ → ℕ) :
    CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ where
  X q := if a ≤ q ∧ q ≤ b then
    SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin (r q))) else 0
  d _ _ := 0

/-- The actual inclusion of the degree-`q` summand in the zero-differential model.
Source: Stacks 09C3, identification of the lifted top cell
(blueprint: lem-sf-projective-cohomology-split-model). -/
def sfSplitCell (a b : ℤ) (r : ℤ → ℕ) (q : ℤ) (hq : a ≤ q ∧ q ≤ b) :
    (CochainComplex.singleFunctor
      (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) q).obj
        (SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin (r q)))) ⟶
      sfSplitComplex C a b r :=
  HomologicalComplex.mkHomFromSingle
    (eqToHom (by dsimp [sfSplitComplex]; rw [ite_eq_left hq]))
    (fun _ _ ↦ by simp [sfSplitComplex])

variable [HasDerivedCategory.{w} (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))]

/-- The cohomology map of an arrow from a finite free sheaf placed in degree `q`.
The single complex in degree `q` is the model for `C^r[-q]`.
Source: Stacks 064B and the generator calculation in Stacks 09C3
(blueprint: lem-sf-projective-cohomology-split-model). -/
def sfFreeCohomologyMap (q : ℤ) (r : ℕ)
    {A : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))}
    (f : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor
        (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) q).obj
        (SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin r)))) ⟶ A) :
    SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin r)) ⟶
      (DerivedCategory.homologyFunctor _ q).obj A :=
  (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) q
      (SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin r)))).inv ≫
    (DerivedCategory.homologyFunctorFactors _ q).inv.app _ ≫
    (DerivedCategory.homologyFunctor _ q).map f

/-- Send a derived arrow to the images of the standard generators in `H^q(A)(U)`.
Source: Stacks 09C3, lifting the sections `rho(e_s)`, and Stacks 064B
(blueprint: lem-sf-projective-cohomology-split-model). -/
def sfShiftedFreeGeneratorMap (q : ℤ) (r : ℕ)
    (A : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)))
    (f : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor
        (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) q).obj
        (SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin r)))) ⟶ A) :
    Fin r → ((DerivedCategory.homologyFunctor _ q).obj A).val.obj
      (op (Scheme.ProEt.mk (𝟙 U))) :=
  fun i ↦ (((DerivedCategory.homologyFunctor _ q).obj A).freeHomEquiv
    (sfFreeCohomologyMap C q r f) (ULift.up i)).val (op (Scheme.ProEt.mk (𝟙 U)))

private theorem projective_single_to_lower_eq_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [Projective P] (n : ℤ) (E : DerivedCategory C) [E.IsLE (n - 1)]
    (f : (DerivedCategory.singleFunctor C n).obj P ⟶ E) : f = 0 := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E (n - 1)
  let := hK
  have h : f ≫ e.hom = 0 :=
    DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
      (f ≫ e.hom) (n - 1) (by omega)
  simpa using (cancel_mono e.hom).1 (by simpa using h)

-- Truncation removes the lower tail without changing maps from P[-n] or H^n.
set_option backward.isDefEq.respectTransparency false in
private theorem sfProjectiveHomologyBijective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [Projective P] (E : DerivedCategory C) (n : ℤ) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor C n).obj P ⟶ E ↦
      (DerivedCategory.homologyFunctor C n).map f) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let S := (DerivedCategory.singleFunctor C n).obj P
  let T := (t.triangleLTGE n).obj E
  have hT := t.triangleLTGE_distinguished n E
  have : t.IsLE T.obj₁ (n - 1) := by
    change t.IsLE ((t.truncLT n).obj E) (n - 1)
    infer_instance
  have hv (f : S ⟶ T.obj₁) : f = 0 := projective_single_to_lower_eq_zero P n _ f
  have hv' (f : S ⟶ T.obj₁⟦(1 : ℤ)⟧) : f = 0 := by
    have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (n - 1) := by
      have := t.isLE_shift T.obj₁ (n - 1) 1 (n - 2) (by omega)
      exact t.isLE_of_le _ (n - 2) (n - 1) (by omega)
    exact projective_single_to_lower_eq_zero P n _ f
  have hpost : Function.Bijective (fun f : S ⟶ E ↦ f ≫ T.mor₂) := by
    constructor
    · intro f g h
      obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT (f - g) (by simp [h])
      rw [hv a, Limits.zero_comp] at ha
      exact sub_eq_zero.mp ha
    · intro g
      obtain ⟨f, hf⟩ := T.coyoneda_exact₃ hT g (hv' (g ≫ T.mor₃))
      exact ⟨f, hf.symm⟩
  let H := DerivedCategory.homologyFunctor C n
  have hH : Function.Bijective (fun f : S ⟶ T.obj₃ ↦ H.map f) :=
    DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n
  have hπ : IsIso (H.map T.mor₂) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app E n n le_rfl
  constructor
  · intro f g h
    apply hpost.1
    apply hH.1
    simpa only [Functor.map_comp] using
      congrArg (fun a ↦ a ≫ H.map T.mor₂) h
  · intro g
    obtain ⟨a, ha⟩ := hH.2 (g ≫ H.map T.mor₂)
    obtain ⟨f, hf⟩ := hpost.2 a
    refine ⟨f, (cancel_mono (H.map T.mor₂)).1 ?_⟩
    change f ≫ T.mor₂ = a at hf
    change H.map a = g ≫ H.map T.mor₂ at ha
    rw [← H.map_comp, hf, ha]

private theorem sfQuasiIsoAtOfCohomologyIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P : A) (q : ℤ) {Z : CochainComplex A ℤ} {N : DerivedCategory A}
    (e : DerivedCategory.Q.obj Z ≅ N)
    (t : (CochainComplex.singleFunctor A q).obj P ⟶ Z)
    (h : IsIso ((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).inv ≫
      (DerivedCategory.homologyFunctorFactors A q).inv.app _ ≫
        (DerivedCategory.homologyFunctor A q).map (DerivedCategory.Q.map t ≫ e.hom))) :
    QuasiIsoAt t q := by
  let H := DerivedCategory.homologyFunctor A q
  let S := (CochainComplex.singleFunctor A q).obj P
  have h₁ : IsIso ((DerivedCategory.homologyFunctorFactors A q).inv.app S ≫
      H.map (DerivedCategory.Q.map t ≫ e.hom)) :=
    (isIso_comp_left_iff
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P).inv _).1 h
  have h₂ : IsIso (H.map (DerivedCategory.Q.map t ≫ e.hom)) :=
    (isIso_comp_left_iff ((DerivedCategory.homologyFunctorFactors A q).inv.app S) _).1 h₁
  have h₃ : IsIso (H.map (DerivedCategory.Q.map t)) := by
    rw [H.map_comp] at h₂
    exact (isIso_comp_right_iff _ (H.map e.hom)).1 h₂
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A q) t).1 h₃

private def sfTerminal : IsTerminal (Scheme.ProEt.mk (𝟙 U)) :=
  IsTerminal.isTerminalOfObj (Scheme.ProEt.forget U) _ Over.mkIdTerminal

private def sfSectionsEquiv
    (M : ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) :
    M.sections ≃ M.val.obj (op (Scheme.ProEt.mk (𝟙 U))) where
  toFun s := s.val _
  invFun x := M.val.sectionsMk
    (fun X ↦ M.val.map (sfTerminal.from X.unop).op x)
    (fun {X Y} f ↦ by
      change M.val.map f (M.val.map (sfTerminal.from X.unop).op x) = _
      rw [← PresheafOfModules.map_comp_apply]
      apply M.val.congr_map_apply
      exact congrArg Quiver.Hom.op (sfTerminal.hom_ext _ _))
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro X
    exact s.property (sfTerminal.from X.unop).op
  right_inv x := by
    have h : sfTerminal.from (Scheme.ProEt.mk (𝟙 U)) = 𝟙 _ :=
      sfTerminal.hom_ext _ _
    change M.val.map (sfTerminal.from (Scheme.ProEt.mk (𝟙 U))).op x = x
    rw [h]
    simp

omit [HasDerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))] in
private theorem sfEvalSurjective
    (hEval : ∀ (F G : Sheaf (Scheme.ProEt.topology U) (Type (max (u + 1) v)))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 U)))))
    {M N : ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)}
    (f : M ⟶ N) [Epi f] :
    Function.Surjective (f.val.app (op (Scheme.ProEt.mk (𝟙 U)))) := by
  let F := SheafOfModules.toSheaf (sfSplitRings.{u, v} C)
  have : PreservesFiniteColimits F :=
    (moduleSheaves_colimits_forgetful (sfSplitRings.{u, v} C)).2.2.1
  have : Epi (F.map f) := preserves_epi_of_preservesColimit F f
  have : Sheaf.IsLocallySurjective (F.map f) :=
    (Sheaf.isLocallySurjective_iff_epi' _ (F.map f)).2 inferInstance
  let G := sheafCompose (Scheme.ProEt.topology U) (forget AddCommGrpCat.{max (u + 1) v})
  have : Epi (G.map (F.map f)) := inferInstance
  exact hEval _ _ (G.map (F.map f)) inferInstance

omit [HasDerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))] in
private theorem sfFreeProjective
    (hEval : ∀ (F G : Sheaf (Scheme.ProEt.topology U) (Type (max (u + 1) v)))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 U)))))
    (I : Type (max (u + 1) v)) :
    Projective (SheafOfModules.free (R := sfSplitRings.{u, v} C) I) where
  factors {M N} f e _ := by
    have hs : Function.Surjective (SheafOfModules.sectionsMap e) := by
      intro s
      obtain ⟨x, hx⟩ := sfEvalSurjective C hEval e ((sfSectionsEquiv C N) s)
      refine ⟨(sfSectionsEquiv C M).symm x, (sfSectionsEquiv C N).injective ?_⟩
      change e.val.app _ ((sfSectionsEquiv C M) ((sfSectionsEquiv C M).symm x)) = _
      rw [Equiv.apply_symm_apply]
      exact hx
    choose t ht using fun i ↦ hs (N.freeHomEquiv f i)
    refine ⟨M.freeHomEquiv.symm t, N.freeHomEquiv.injective ?_⟩
    funext i
    simpa only [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply] using ht i

set_option backward.isDefEq.respectTransparency.types false in
private theorem sfFreeCohomologyBijective
    (hEval : ∀ (F G : Sheaf (Scheme.ProEt.topology U) (Type (max (u + 1) v)))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 U)))))
    (q : ℤ) (r : ℕ)
    (A : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))) :
    Function.Bijective (sfFreeCohomologyMap C q r (A := A)) := by
  let P := SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin r))
  have : Projective P := sfFreeProjective C hEval _
  let S := (CochainComplex.singleFunctor _ q).obj P
  let H := DerivedCategory.homologyFunctor
    (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) q
  let ε : H.obj (DerivedCategory.Q.obj S) ≅ P :=
    (DerivedCategory.homologyFunctorFactors _ q).app S ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q P
  have hb : Function.Bijective (H.map : (DerivedCategory.Q.obj S ⟶ A) →
      (H.obj (DerivedCategory.Q.obj S) ⟶ H.obj A)) := sfProjectiveHomologyBijective P A q
  have he := (Iso.homCongr ε (Iso.refl (H.obj A))).bijective.comp hb
  have heval (f : DerivedCategory.Q.obj S ⟶ A) :
      (Iso.homCongr ε (Iso.refl (H.obj A))) (H.map f) =
        sfFreeCohomologyMap C q r f := by
    change (ε.inv ≫ H.map f ≫ 𝟙 _) = _
    simp only [Category.comp_id]
    dsimp [ε, sfFreeCohomologyMap]
    simp only [Category.assoc]
    rfl
  change Function.Bijective (fun f : DerivedCategory.Q.obj S ⟶ A ↦ sfFreeCohomologyMap C q r f)
  simpa only [Function.comp_def, heval] using he

private def sfFreeSectionsEquiv
    (M : ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) (r : ℕ) :
    (SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin r)) ⟶ M) ≃
      (Fin r → M.val.obj (op (Scheme.ProEt.mk (𝟙 U)))) where
  toFun f i := sfSectionsEquiv C M (M.freeHomEquiv f (ULift.up i))
  invFun s := M.freeHomEquiv.symm (fun i ↦ (sfSectionsEquiv C M).symm (s i.down))
  left_inv f := by
    apply M.freeHomEquiv.injective
    funext i
    cases i
    simp
  right_inv s := by simp

/-- Bounded-above projective module complexes represent all derived maps, with equality
exactly chain homotopy (`f-g = dh+hd` in Mathlib's Homotopy convention).
Source: Stacks 064B, lemma-morphisms-from-projective-complex
(blueprint: lem-sf-projective-cohomology-split-model).

Proof: Apply lem-sc-bounded-above-projective-kprojective to P and its bound d.
Then lem-coef-kprojective-derived-hom-bijection identifies homotopy-category maps
out of P with derived maps. The quotient functor from complexes is full, and
its fibers are precisely Nonempty (Homotopy f g). Transport along the canonical
quotient/localization comparison gives the two assertions for Q itself. No enough
projectives hypothesis and no boundedness on L are required. -/
theorem sf_bounded_above_projective_chain_representatives
    (P : CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ)
    (d : ℤ) [P.IsStrictlyLE d] [∀ n : ℤ, Projective (P.X n)]
    (L : CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ) :
    (∀ phi : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L,
      ∃ f : P ⟶ L, DerivedCategory.Q.map f = phi) ∧
    (∀ f g : P ⟶ L, DerivedCategory.Q.map f = DerivedCategory.Q.map g ↔
      Nonempty (Homotopy f g)) := by
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P d
  let H := HomotopyCategory.quotient
    (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso
    (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))
  have hb := CochainComplex.IsKProjective.Qh_map_bijective P (H.obj L)
  constructor
  · intro phi
    obtain ⟨g, hg⟩ := hb.surjective (e.hom.app P ≫ phi ≫ e.inv.app L)
    obtain ⟨f, rfl⟩ := H.map_surjective g
    refine ⟨f, ?_⟩
    apply (cancel_mono (e.inv.app L)).1
    rw [DerivedCategory.quotientCompQhIso_inv_naturality]
    dsimp [H] at hg
    rw [hg]
    dsimp [e]
    simp
  · intro f g
    constructor
    · intro h
      apply Nonempty.intro
      apply HomotopyCategory.homotopyOfEq f g
      apply hb.injective
      apply (cancel_epi (e.inv.app P)).1
      change (DerivedCategory.quotientCompQhIso _).inv.app P ≫ _ =
        (DerivedCategory.quotientCompQhIso _).inv.app P ≫ _
      rw [← DerivedCategory.quotientCompQhIso_inv_naturality,
        ← DerivedCategory.quotientCompQhIso_inv_naturality, h]
    · rintro ⟨h⟩
      apply (cancel_mono (e.inv.app L)).1
      change DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso _).inv.app L =
        DerivedCategory.Q.map g ≫ (DerivedCategory.quotientCompQhIso _).inv.app L
      rw [DerivedCategory.quotientCompQhIso_inv_naturality,
        DerivedCategory.quotientCompQhIso_inv_naturality,
        HomotopyCategory.eq_of_homotopy f g h]

omit [HasDerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))] in
private theorem sfCellComponentIso (a b : ℤ) (r : ℤ → ℕ) (q : ℤ)
    (hq : a ≤ q ∧ q ≤ b) : IsIso ((sfSplitCell C a b r q hq).f q) := by
  dsimp [sfSplitCell]
  rw [HomologicalComplex.mkHomFromSingle_f]
  infer_instance

omit [HasDerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))] in
private theorem sfCellHomologyIso (a b : ℤ) (r : ℤ → ℕ) (q : ℤ)
    (hq : a ≤ q ∧ q ≤ b) :
    IsIso (HomologicalComplex.homologyMap (sfSplitCell C a b r q hq) q) := by
  let S := (CochainComplex.singleFunctor _ q).obj
    (SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin (r q))))
  let V := sfSplitComplex C a b r
  let f : S ⟶ V := sfSplitCell C a b r q hq
  have : IsIso (f.f q) := sfCellComponentIso C a b r q hq
  have : IsIso (S.iCycles q) := S.isIso_iCycles q _ rfl rfl
  have : IsIso (V.iCycles q) := V.isIso_iCycles q _ rfl rfl
  have : IsIso (S.homologyπ q) := S.isIso_homologyπ _ q rfl rfl
  have : IsIso (V.homologyπ q) := V.isIso_homologyπ _ q rfl rfl
  have : IsIso (HomologicalComplex.cyclesMap f q ≫ V.iCycles q) := by
    rw [HomologicalComplex.cyclesMap_i]
    infer_instance
  have : IsIso (HomologicalComplex.cyclesMap f q) :=
    IsIso.of_isIso_comp_right _ (V.iCycles q)
  have : IsIso (S.homologyπ q ≫ HomologicalComplex.homologyMap f q) := by
    rw [HomologicalComplex.homologyπ_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (S.homologyπ q) _

omit [HasDerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))] in
private def sfAssembledMap (a b : ℤ) (r : ℤ → ℕ)
    (Z : CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ)
    (t : ∀ (q : ℤ) (_hq : a ≤ q ∧ q ≤ b),
      (CochainComplex.singleFunctor _ q).obj
        (SheafOfModules.free (R := sfSplitRings.{u, v} C)
          (ULift.{max (u + 1) v} (Fin (r q)))) ⟶ Z) :
    sfSplitComplex C a b r ⟶ Z := by
  classical
  have hcell (q : ℤ) (hq : a ≤ q ∧ q ≤ b) :
      IsIso ((sfSplitCell C a b r q hq).f q) := sfCellComponentIso C a b r q hq
  exact
    { f q := if hq : a ≤ q ∧ q ≤ b then
        inv ((sfSplitCell C a b r q hq).f q) ≫ (t q hq).f q
        else 0
      comm' q k hqk := by
        change _ ≫ Z.d q k = (0 : (sfSplitComplex C a b r).X q ⟶ _) ≫ _
        rw [zero_comp]
        split_ifs with hq
        · rw [Category.assoc, (t q hq).comm q k]
          simp
        · simp }

omit [HasDerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))] in
private theorem sfAssembledMap_cell (a b : ℤ) (r : ℤ → ℕ)
    (Z : CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ)
    (t : ∀ (q : ℤ) (_hq : a ≤ q ∧ q ≤ b),
      (CochainComplex.singleFunctor _ q).obj
        (SheafOfModules.free (R := sfSplitRings.{u, v} C)
          (ULift.{max (u + 1) v} (Fin (r q)))) ⟶ Z)
    (q : ℤ) (hq : a ≤ q ∧ q ≤ b) :
    sfSplitCell C a b r q hq ≫ sfAssembledMap C a b r Z t = t q hq := by
  have : IsIso ((sfSplitCell C a b r q hq).f q) := sfCellComponentIso C a b r q hq
  apply HomologicalComplex.from_single_hom_ext
  change (sfSplitCell C a b r q hq).f q ≫ (sfAssembledMap C a b r Z t).f q = _
  dsimp only [sfAssembledMap]
  rw [dite_eq_left hq]
  simp only [IsIso.hom_inv_id_assoc]

private theorem sfFreeCohomologyQuasiIsoAt (q : ℤ) (r : ℕ)
    {Z : CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ}
    {N : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))}
    (e : DerivedCategory.Q.obj Z ≅ N)
    (t : (CochainComplex.singleFunctor _ q).obj
      (SheafOfModules.free (R := sfSplitRings.{u, v} C)
        (ULift.{max (u + 1) v} (Fin r))) ⟶ Z)
    (h : IsIso (sfFreeCohomologyMap C q r (DerivedCategory.Q.map t ≫ e.hom))) :
    QuasiIsoAt t q :=
  sfQuasiIsoAtOfCohomologyIso _ q e t h

attribute [local irreducible] sfAssembledMap

/-- Prescribed finite free cohomology gives a chain quasi-isomorphism from its split model;
any derived arrow inducing the top prescribed isomorphism is its top-cell inclusion.
Source: Stacks 09C3, generator lifting, expanded degreewise; Stacks 064B
(blueprint: lem-sf-projective-cohomology-split-model).

Proof:
1. The exact forgetful functor to abelian sheaves preserves epimorphisms
   (situation-conventions). The local-surjectivity criteria for
   abelian sheaves and set sheaves identify their underlying maps as epimorphisms of
   set sheaves. The evaluation hypothesis therefore makes module quotients surjective
   on sections at U; kernels are sectionwise.
2. A map from a finite free module sheaf is determined by its generator sections at
   the terminal object U. Lift those sections through any epimorphism. This proves
   projectivity, including rank zero.
3. Step 5 lifts each theta to a derived arrow from the single free term. Compose with
   e.inv and apply step 4 to obtain a representative chain map. Assemble these maps by
   inverting each actual cell's component in its degree, and put zero outside [a,b].
   The resulting chain map v restricts to the chosen representative on every cell.
   Its cohomology maps are exactly theta. The cells are isomorphisms on cohomology in
   their degrees; outside the interval both cohomologies vanish. Thus v is a quasi-isomorphism.
4. Bounded-above projective complexes are K-projective by
   lem-sc-bounded-above-projective-kprojective; their derived arrows are homotopy classes
   by lem-coef-kprojective-derived-hom-bijection, with no target boundedness requirement.
5. For a projective single term P[-q], maps into an object in degrees at most q-1
   vanish. The canonical truncation triangle and its exact Hom sequence therefore
   identify maps into A with maps into its truncation in degrees at least q. On that
   truncation the shifted-heart comparison computes maps by H^q, and the truncation
   projection induces an isomorphism on H^q. The canonical single-object and localization
   comparisons give precisely sfFreeCohomologyMap. The free-sheaf and terminal-section
   equivalences give the specified generator bijection. Functoriality proves naturality.
6. The top cell followed by v induces theta_b. By step 5 any other arrow with that
   cohomology map is equal to it, giving the stated summand identification. -/
theorem sf_projective_cohomology_split_model
    (hEval : ∀ (F G : Sheaf (Scheme.ProEt.topology U) (Type (max (u + 1) v)))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 U)))))
    (N : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)))
    (a b : ℤ) (hab : a ≤ b) (r : ℤ → ℕ)
    (hN : ∀ q : ℤ, ¬ (a ≤ q ∧ q ≤ b) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj N))
    (theta : ∀ (q : ℤ) (_hq : a ≤ q ∧ q ≤ b),
      SheafOfModules.free (R := sfSplitRings.{u, v} C) (ULift.{max (u + 1) v} (Fin (r q))) ≅
        (DerivedCategory.homologyFunctor _ q).obj N)
    (Z : CochainComplex (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) ℤ)
    (e : DerivedCategory.Q.obj Z ≅ N) :
    ∃ v : sfSplitComplex C a b r ⟶ Z,
      QuasiIso v ∧
      (∀ (q : ℤ) (hq : a ≤ q ∧ q ≤ b),
        sfFreeCohomologyMap C q (r q)
          (DerivedCategory.Q.map (sfSplitCell C a b r q hq ≫ v) ≫ e.hom) =
          (theta q hq).hom) ∧
      (∀ f : DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor
            (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) b).obj
            (SheafOfModules.free (R := sfSplitRings.{u, v} C)
              (ULift.{max (u + 1) v} (Fin (r b))))) ⟶ N,
        sfFreeCohomologyMap C b (r b) f = (theta b ⟨hab, le_refl b⟩).hom →
        f = DerivedCategory.Q.map (sfSplitCell C a b r b ⟨hab, le_refl b⟩ ≫ v) ≫ e.hom) := by
  classical
  let : Category (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) :=
    inferInstance
  let : Abelian (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) :=
    inferInstance
  let : Category (DerivedCategory
      (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))) := inferInstance
  let F (q : ℤ) := SheafOfModules.free (R := sfSplitRings.{u, v} C)
    (ULift.{max (u + 1) v} (Fin (r q)))
  let S (q : ℤ) := (CochainComplex.singleFunctor _ q).obj (F q)
  have hrep (q : ℤ) (hq : a ≤ q ∧ q ≤ b) :
      ∃ t : S q ⟶ Z,
        sfFreeCohomologyMap C q (r q) (DerivedCategory.Q.map t ≫ e.hom) =
          (theta q hq).hom := by
    obtain ⟨φ, hφ⟩ := (sfFreeCohomologyBijective C hEval q (r q) N).surjective
      (theta q hq).hom
    have : ∀ n : ℤ, Projective ((S q).X n) := by
      intro n
      by_cases hn : n = q
      · subst n
        exact Projective.of_iso
          (HomologicalComplex.singleObjXSelf (.up ℤ) q (F q)).symm
          (sfFreeProjective C hEval _)
      · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) q (F q) n hn).projective
    obtain ⟨t, ht⟩ :=
      (sf_bounded_above_projective_chain_representatives C (S q) q Z).1 (φ ≫ e.inv)
    refine ⟨t, ?_⟩
    simpa only [ht, Category.assoc, e.inv_hom_id, Category.comp_id] using hφ
  choose t ht using hrep
  let v := sfAssembledMap C a b r Z t
  have hv (q : ℤ) (hq : a ≤ q ∧ q ≤ b) :
      sfSplitCell C a b r q hq ≫ v = t q hq := sfAssembledMap_cell C a b r Z t q hq
  have hθ (q : ℤ) (hq : a ≤ q ∧ q ≤ b) :
      sfFreeCohomologyMap C q (r q)
        (DerivedCategory.Q.map (sfSplitCell C a b r q hq ≫ v) ≫ e.hom) =
          (theta q hq).hom := by
    rw [hv]
    exact ht q hq
  refine ⟨v, ⟨fun q ↦ ?_⟩, hθ, ?_⟩
  · by_cases hq : a ≤ q ∧ q ≤ b
    · have : QuasiIsoAt (sfSplitCell C a b r q hq) q :=
        (quasiIsoAt_iff_isIso_homologyMap _ _).2 (sfCellHomologyIso C a b r q hq)
      have hf := (theta q hq).isIso_hom
      rw [← hθ q hq] at hf
      have : QuasiIsoAt (sfSplitCell C a b r q hq ≫ v) q :=
        sfFreeCohomologyQuasiIsoAt C q (r q) e (sfSplitCell C a b r q hq ≫ v) hf
      exact (quasiIsoAt_iff_comp_left (sfSplitCell C a b r q hq) v q).1 inferInstance
    · have hV : IsZero ((sfSplitComplex C a b r).X q) := by
        dsimp [sfSplitComplex]
        rw [ite_eq_right hq]
        exact isZero_zero _
      have hHZ : IsZero (Z.homology q) :=
        (hN q hq).of_iso
          (((DerivedCategory.homologyFunctor _ q).mapIso e).symm ≪≫
            (DerivedCategory.homologyFunctorFactors _ q).app Z).symm
      rw [quasiIsoAt_iff_isIso_homologyMap]
      exact (HomologicalComplex.ExactAt.of_isZero hV).isZero_homology.isIso hHZ _
  · intro f hf
    exact (sfFreeCohomologyBijective C hEval b (r b) N).injective
      (hf.trans (hθ b ⟨hab, le_rfl⟩).symm)

/-- The specified generator-section map is bijective, naturally in the derived target.
Source: Stacks 064B; Stacks 09C3, lifting `rho(e_s)`
(blueprint: lem-sf-projective-cohomology-split-model).

Proof: Steps 1--2 of sf_projective_cohomology_split_model make each finite free term
projective. Its derived maps are computed by cohomology using the canonical truncation
triangle, projective-source vanishing, and the shifted-heart comparison as in step 5.
Transport along the canonical single-object and localization comparisons gives the
specified cohomology map. The free-sheaf equivalence and evaluation at the terminal
object identify its values with the prescribed generator sections, proving bijectivity.
Functoriality of derived cohomology and evaluation on the standard free generators
proves the naturality equation for all derived arrows. -/
theorem sf_shifted_free_generator_bijective_natural
    (hEval : ∀ (F G : Sheaf (Scheme.ProEt.topology U) (Type (max (u + 1) v)))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 U))))) :
    (∀ (q : ℤ) (r : ℕ)
      (A : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C))),
      Function.Bijective (sfShiftedFreeGeneratorMap C q r A)) ∧
    (∀ (q : ℤ) (r : ℕ)
      (A B : DerivedCategory (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)))
      (alpha : A ⟶ B)
      (f : DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor
        (ringedSiteModules.{max (u + 1) v} (sfSplitRings.{u, v} C)) q).obj
          (SheafOfModules.free (R := sfSplitRings.{u, v} C)
            (ULift.{max (u + 1) v} (Fin r)))) ⟶ A) (i : Fin r),
      sfShiftedFreeGeneratorMap C q r B (f ≫ alpha) i =
        ((DerivedCategory.homologyFunctor _ q).map alpha).val.app
          (op (Scheme.ProEt.mk (𝟙 U))) (sfShiftedFreeGeneratorMap C q r A f i)) := by
  constructor
  · intro q r A
    exact (sfFreeSectionsEquiv C _ r).bijective.comp (sfFreeCohomologyBijective C hEval q r A)
  · intro q r A B alpha f i
    have h : sfFreeCohomologyMap C q r (f ≫ alpha) =
        sfFreeCohomologyMap C q r f ≫ (DerivedCategory.homologyFunctor _ q).map alpha := by
      simp only [sfFreeCohomologyMap, Functor.map_comp, Category.assoc]
    simp only [sfShiftedFreeGeneratorMap, h, SheafOfModules.freeHomEquiv_comp_apply]
    rfl

end WeilConjectures
