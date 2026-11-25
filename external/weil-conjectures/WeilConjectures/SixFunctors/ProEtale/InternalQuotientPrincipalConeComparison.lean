/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalConeTower
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import all WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.SixFunctors.ProEtale.InternalPrincipalConeLevelAugmentation

/-! # The internal quotient and principal cone comparison

Source: Stacks Project, Tags 099B, 0A0E and 0941.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.AdicCompletion

private theorem zeroLift_f (M : Type*) [Category* M] [Abelian M]
    {C K L : CochainComplex M ℤ} (φ : K ⟶ L) (u : C ⟶ K)
    (hu : u ≫ φ = 0) (p : ℤ) :
    (CochainComplex.mappingCocone.lift φ u 0 (by simp [hu])).f p =
      u.f p ≫ (CochainComplex.mappingCocone.inl φ).v p p (add_zero p) := by
  let l := CochainComplex.mappingCocone.lift φ u 0 (by simp [hu])
  have h := CochainComplex.mappingCocone.id_X φ p (p + -1) rfl
  calc
    l.f p = l.f p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = _ := by
      rw [← h, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        CochainComplex.mappingCocone.lift_f_fst_f,
        CochainComplex.mappingCocone.lift_f_snd_v]
      simp

private theorem zeroLift_natural (M : Type*) [Category* M] [Abelian M]
    {C D K₁ K₂ L₁ L₂ : CochainComplex M ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (α : C ⟶ D) (u : C ⟶ K₁) (v : D ⟶ K₂)
    (hu : u ≫ φ₁ = 0) (hv : v ≫ φ₂ = 0) (hn : α ≫ v = u ≫ a) :
    α ≫ CochainComplex.mappingCocone.lift φ₂ v 0 (by simp [hv]) =
      CochainComplex.mappingCocone.lift φ₁ u 0 (by simp [hu]) ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧' := by
  apply HomologicalComplex.hom_ext
  intro p
  have hi : (CochainComplex.mappingCocone.inl φ₁).v p p (add_zero p) ≫
      ((CochainComplex.mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧').f p =
      a.f p ≫ (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p) := by
    simp [CochainComplex.mappingCocone.inl,
      CochainComplex.HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
      CochainComplex.mappingCone.map]
  simp only [HomologicalComplex.comp_f]
  rw [zeroLift_f M φ₂ v hv p, zeroLift_f M φ₁ u hu p,
    Category.assoc, hi, ← Category.assoc]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun z ↦ z.f p ≫
      (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p)) hn

private theorem quotientTowerComparison
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    [HasExactLimitsOfShape (Discrete ℕ) A] [HasDerivedCategory A]
    {P : CochainComplex A ℤ} (μ : End P) (V : ℕ → CochainComplex A ℤ)
    (t : ∀ n, V (n + 1) ⟶ V n)
    (u : ∀ n : ℕ, P ⟶ V n)
    (hv : Pi.lift u ≫ towerTransitionEndomorphism
      (K := fun n ↦ V n) t = 0)
    (a : ∀ n, CochainComplex.PrincipalCone.level μ n ⟶ V n)
    (ha : ∀ n, QuasiIso (a n))
    (hs : ∀ n, CochainComplex.PrincipalCone.step μ n ≫ a n =
      a (n + 1) ≫ t n)
    (hu : ∀ n, CochainComplex.mappingCone.inr (μ ^ (n + 1)).asHom ≫ a n = u n) :
    ∃ c : DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion μ) ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCocone (towerTransitionEndomorphism t)),
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫ c.hom =
        DerivedCategory.Q.map (CochainComplex.mappingCocone.lift _ (Pi.lift u) 0
          (by simp [hv])) := by
  classical
  let p : (∏ᶜ fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n)) ⟶
      ∏ᶜ (fun n ↦ V n) := Limits.Pi.map
    (f := fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n))
    (g := fun n ↦ V n) a
  let f := CochainComplex.PrincipalCone.oneSubShift μ
  let g := towerTransitionEndomorphism (K := fun n ↦ V n)
    t
  have hfg : f ≫ p = p ≫ g := by
    exact (towerTransitionEndomorphism_natural_backward
      (K := fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n))
      (K' := fun n ↦ V n)
      (CochainComplex.PrincipalCone.step μ) t a
      (fun n ↦ (hs n).symm)).symm
  have (n : Discrete ℕ) : QuasiIso
      ((Discrete.natTrans
        (F := Discrete.functor (fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n)))
        (G := Discrete.functor (fun n ↦ V n))
        (fun n ↦ a n.as)).app n) := ha n.as
  have hp : QuasiIso p := HomologicalComplex.quasiIso_limMap
    (Discrete.natTrans (F := Discrete.functor
      (fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n)))
      (G := Discrete.functor (fun n ↦ V n)) (fun n ↦ a n.as))
  let m := CochainComplex.mappingCone.map f g p p hfg
  let τ := CochainComplex.mappingCone.triangleMap f g p p hfg
  have hm : IsIso (DerivedCategory.Q.map m) :=
    Pretriangulated.isIso₃_of_isIso₁₂ (DerivedCategory.Q.mapTriangle.map τ)
      (DerivedCategory.mappingCone_triangle_distinguished f)
      (DerivedCategory.mappingCone_triangle_distinguished g)
      (inferInstance : IsIso (DerivedCategory.Q.map p))
      (inferInstance : IsIso (DerivedCategory.Q.map p))
  have : QuasiIso m := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hm
  let b := m⟦(-1 : ℤ)⟧'
  have : QuasiIso b := inferInstance
  let c := asIso (DerivedCategory.Q.map b)
  have hn : (𝟙 P) ≫ Pi.lift u = CochainComplex.PrincipalCone.productUnit μ ≫ p := by
    apply Pi.hom_ext
    intro n
    simp only [Category.id_comp, p, Category.assoc, Limits.Pi.map_π,
      CochainComplex.PrincipalCone.productUnit, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    exact (hu n).symm
  have hb : CochainComplex.PrincipalCone.unit μ ≫ b =
      CochainComplex.mappingCocone.lift g (Pi.lift u) 0 (by
        have hv' : Pi.lift u ≫ g = 0 := hv
        simp only [CochainComplex.HomComplex.δ_zero, zero_add, hv',
          CochainComplex.HomComplex.Cochain.ofHom_zero]) := by
    simpa only [Category.id_comp, CochainComplex.PrincipalCone.unit, b, m, f] using
      (zeroLift_natural A f g p p hfg (𝟙 P)
        (CochainComplex.PrincipalCone.productUnit μ) (Pi.lift u)
        (CochainComplex.PrincipalCone.productUnit_comp μ) hv hn).symm
  refine ⟨c, ?_⟩
  change DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫
    DerivedCategory.Q.map b = _
  rw [← Functor.map_comp, hb]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The strict quotient Roos complex agrees with the principal cone completion,
including its specified augmentation.
Source: Stacks 0A0E, the regular principal Koszul-to-quotient comparison, and 0941.
(auxiliary; not a blueprint node).

Proof: use the coefficient resolution 0 -> R --pi^(n+1)--> R -> B_n -> 0.
Its cone augmentation to B_n[0] is a quasi-isomorphism. Tensor with a K-flat P;
the tensor cone is the mapping cone of scalar multiplication by pi^(n+1) on P.
The comparison is compatible with transitions (pi,1) and the specified quotient
transition, since both composites to B_n are quotient projection. The degree-zero
cone inclusion goes to p tensor 1. Take products and mapping cocones. Exact countable
products preserve the level quasi-isomorphisms, so the induced Roos comparison is a
quasi-isomorphism. The signed coordinate interchange identifies its source with the
principal mapping cocone and its target with the internal coordinates (x,y), whose
differential is (dx,(1-s)x-dy). It takes the strict zero-homotopy augmentation to
(unit,0). Localizing this chain comparison gives the asserted unit-compatible iso.
No flatness of the terms of P is needed: K-flat tensoring preserves the coefficient
resolution quasi-isomorphism. The zero complex and empty scheme give zero objects. -/
theorem internal_quotient_principal_cone_comparison
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (f : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) f).down s =
        Padic.coefficientExtensionUniformizer l E * f.down s)
    (P : CochainComplex (Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P) :
    ∃ c : DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion
        (End.of (DerivedNakayama.scalarOnComplex l E X d P))) ≅
        DerivedCategory.Q.obj (roos l E X P),
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
        (End.of (DerivedNakayama.scalarOnComplex l E X d P))) ≫ c.hom =
        DerivedCategory.Q.map (augmentation l E X P) := by
  classical
  let μ : End P := .of (DerivedNakayama.scalarOnComplex l E X d P)
  choose a ha hc using fun n ↦ internal_principal_cone_level_augmentation l E X d hd P hP n
  have hc' (n : ℕ) (q : ℤ) : (a n).f q =
      (CochainComplex.mappingCone.snd (μ ^ (n + 1)).asHom).v q q (add_zero q) ≫
        (levelUnit l E X P n).f q := hc n q
  have hs (n : ℕ) : CochainComplex.PrincipalCone.step μ n ≫ a n =
      a (n + 1) ≫ levelStep l E X P n := by
    apply HomologicalComplex.hom_ext
    intro q
    apply CochainComplex.mappingCone.ext_from (μ ^ (n + 1 + 1)).asHom (q + 1) q rfl
    · simp [HomologicalComplex.comp_f, hc', CochainComplex.PrincipalCone.step,
        CochainComplex.mappingCone.map]
    · have h := congrArg (fun k ↦ k.f q) (levelUnit_step l E X P n)
      simpa [HomologicalComplex.comp_f, hc', CochainComplex.PrincipalCone.step,
        CochainComplex.mappingCone.map, Category.assoc] using h.symm
  have hu (n : ℕ) : CochainComplex.mappingCone.inr (μ ^ (n + 1)).asHom ≫ a n =
      levelUnit l E X P n := by
    ext q
    simp only [HomologicalComplex.comp_f, hc',
      CochainComplex.mappingCone.inr_f_snd_v_assoc]
  let := modules_countableAB4Star l E X
  obtain ⟨c, hc⟩ := quotientTowerComparison μ
    (fun n ↦ (level l E X n).obj P) (levelStep l E X P)
    (levelUnit l E X P) (unitProduct_oneSubShift l E X P) a ha hs hu
  let e : CochainComplex.mappingCocone (oneSubShift l E X P) ≅ roos l E X P :=
    genericCoconeIso (product l E X P) (oneSubShift l E X P)
  refine ⟨c ≪≫ DerivedCategory.Q.mapIso e, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, hc, Functor.mapIso_hom, ← Functor.map_comp]
  apply DerivedCategory.Q.congr_map
  ext q
  change (CochainComplex.mappingCocone.lift (oneSubShift l E X P)
    (unitProduct l E X P) 0 _).f q ≫
      (genericCoconeCoordinateIso (product l E X P) (oneSubShift l E X P) q).hom =
        biprod.lift ((unitProduct l E X P).f q) 0
  apply biprod.hom_ext <;>
    simp [genericCoconeCoordinateIso, Category.assoc]

end AlgebraicGeometry.ProEtale.AdicCompletion
