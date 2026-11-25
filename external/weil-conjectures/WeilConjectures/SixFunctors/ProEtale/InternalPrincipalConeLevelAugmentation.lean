/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalConeTower
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-! # A normalized internal principal-cone augmentation at one quotient level

Source: Stacks Project, Tags 0A0E and 06YY.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale.AdicCompletion

section Generic
universe v w
open MonoidalCategory
variable {A : Type v} [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {R : Type*} [CommRing R] [Linear R A] [MonoidalLinear R A]

private def tensorUnitMap {B : A} (p : 𝟙_ A ⟶ B) :
    𝟭 (CochainComplex A ℤ) ⟶ (tensorRight B).mapHomologicalComplex (.up ℤ) :=
  NatTrans.mapHomologicalComplex
    ((rightUnitorNatIso A).inv ≫ (tensoringRight A).map p) (.up ℤ)

omit [IsGrothendieckAbelian A] [HasDerivedCategory A] [MonoidalClosed A]
  [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A] in
private theorem scalar_tensorUnitMap_zero {B : A} (r : R) (p : 𝟙_ A ⟶ B)
    (w : (r • 𝟙 (𝟙_ A)) ≫ p = 0) (P : CochainComplex A ℤ) :
    (r • 𝟙 P) ≫ (tensorUnitMap p).app P = 0 := by
  ext q
  change (r • 𝟙 (P.X q)) ≫ ((ρ_ (P.X q)).inv ≫ P.X q ◁ p) = 0
  calc
    _ = (ρ_ (P.X q)).inv ≫ P.X q ◁ ((r • 𝟙 (𝟙_ A)) ≫ p) := by
      simp [Linear.smul_comp, Linear.comp_smul, MonoidalLinear.whiskerLeft_smul]
    _ = 0 := by rw [w]; simp

private theorem normalized_scalar_augmentation {B : A} (r : R) (p : 𝟙_ A ⟶ B)
    (w : (r • 𝟙 (𝟙_ A)) ≫ p = 0)
    (hs : (ShortComplex.mk _ _ w).ShortExact)
    (P : CochainComplex A ℤ)
    (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P) :
    ∃ a : CochainComplex.mappingCone (r • 𝟙 P) ⟶
        ((tensorRight B).mapHomologicalComplex (.up ℤ)).obj P,
      QuasiIso a ∧ ∀ q : ℤ, a.f q =
        (CochainComplex.mappingCone.snd (r • 𝟙 P)).v q q (add_zero q) ≫
          ((tensorUnitMap p).app P).f q := by
  let T := (tensorRight B).mapHomologicalComplex (.up ℤ)
  let S (K : CochainComplex A ℤ) := ShortComplex.mk
    (r • 𝟙 K) ((tensorUnitMap p).app K) (scalar_tensorUnitMap_zero r p w K)
  let a (K : CochainComplex A ℤ) := CochainComplex.mappingCone.descShortComplex (S K)
  have hflat (K : CochainComplex A ℤ) (hK : ∀ q, ObjectProperty.flat (K.X q)) :
      QuasiIso (a K) := by
    apply CochainComplex.mappingCone.quasiIso_descShortComplex
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro q
    have : PreservesFiniteLimits (tensorLeft (K.X q)) := (hK q).1.1
    let e : (ShortComplex.mk _ _ w).map (tensorLeft (K.X q)) ≅
        (S K).map (HomologicalComplex.eval A (.up ℤ) q) :=
      ShortComplex.isoMk (ρ_ (K.X q)) (ρ_ (K.X q)) (Iso.refl _)
        (by
          change (ρ_ (K.X q)).hom ≫ (r • 𝟙 K).f q =
            (tensorLeft (K.X q)).map (r • 𝟙 (𝟙_ A)) ≫ (ρ_ (K.X q)).hom
          rw [Functor.map_smul, (tensorLeft (K.X q)).map_id]
          change (ρ_ (K.X q)).hom ≫ (r • 𝟙 (K.X q)) =
            (r • 𝟙 (K.X q ⊗ 𝟙_ A)) ≫ (ρ_ (K.X q)).hom
          rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp])
        (by simp [S, tensorUnitMap])
    exact ShortComplex.shortExact_of_iso e (hs.map_of_exact _)
  obtain ⟨K, f, hf, hterms, hK⟩ := CochainComplex.exists_quasiIso_flat_kFlat P
  have : QuasiIso f := hf
  let c := CochainComplex.mappingCone.map (r • 𝟙 K) (r • 𝟙 P) f f (by simp)
  have : QuasiIso c := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso A c).mp
    exact Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map
        (CochainComplex.mappingCone.triangleMap (r • 𝟙 K) (r • 𝟙 P) f f (by simp)))
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (inferInstance : IsIso (DerivedCategory.Q.map f))
      (inferInstance : IsIso (DerivedCategory.Q.map f))
  have : QuasiIso (a K) := hflat K hterms
  let F := tensorRight B
  let : F.PreservesKFlatQuasiIso := Functor.PreservesKFlatQuasiIso.mk' F
    (fun L hL hLa ↦ CochainComplex.acyclic_tensorRight_of_kFlat L hL hLa B)
  have : QuasiIso (T.map f) := F.quasiIso_mapHomologicalComplex_map_of_kFlat hK hP f
  have hn : c ≫ a P = a K ≫ T.map f := by
    let φ : S K ⟶ S P :=
      { τ₁ := f
        τ₂ := f
        τ₃ := T.map f
        comm₁₂ := by simp [S]
        comm₂₃ := (tensorUnitMap p).naturality f }
    exact CochainComplex.mappingCone.map_descShortComplex (S K) (S P) φ
  have : QuasiIso (c ≫ a P) := by rw [hn]; infer_instance
  refine ⟨a P, quasiIso_of_comp_left c (a P), ?_⟩
  intro q
  simp [a, CochainComplex.mappingCone.descShortComplex,
    CochainComplex.mappingCone.desc_f _ _ _ _ q (q + 1) rfl, S]

end Generic

private theorem conjugateFunctor_pow {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {U : C} {V : D} (e : F.obj U ≅ V) (d : End U) (k : ℕ) :
    e.inv ≫ F.map (d ^ k).asHom ≫ e.hom =
      (End.of (e.inv ≫ F.map d.asHom ≫ e.hom) ^ k).asHom := by
  induction k with
  | zero =>
    change e.inv ≫ F.map (𝟙 U) ≫ e.hom = 𝟙 V
    rw [F.map_id, Category.id_comp, Iso.inv_hom_id]
  | succ k ih =>
    simpa only [pow_succ, End.mul_asHom, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_assoc] using
      congrArg (fun t ↦ (e.inv ≫ F.map d.asHom ≫ e.hom) ≫ t) ih

private theorem complexAction_pow {A : Type*} [Category* A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A]
    (P : CochainComplex A ℤ) (μ : End P) (r : End (𝟙_ A))
    (hμ : ∀ q, μ.asHom.f q = (unitEndAction (P.X q) r).asHom) (k : ℕ) (q : ℤ) :
    (μ ^ k).asHom.f q = (unitEndAction (P.X q) (r ^ k)).asHom := by
  induction k with
  | zero =>
    change 𝟙 (P.X q) = (unitEndAction (P.X q) (1 : End (𝟙_ A))).asHom
    rw [map_one]
    rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, map_mul, End.mul_asHom, End.mul_asHom,
      HomologicalComplex.comp_f, ih, hμ]

/-- The normalized cone augmentation computes one positive quotient on a K-flat complex.

Source: Stacks Project, Tag 0A0E, regular singleton Koszul-to-quotient comparison,
and Tag 06YY, K-flat tensor computation.
(auxiliary; not a blueprint node).

Proof: the pointwise formula determines d as multiplication by the uniformizer.
Pull back the exact coefficient sequence R --pi^(n+1)--> R --> B_n.
The corresponding two-term cone augments quasi-isomorphically to B_n in degree zero,
with the quotient map on its unshifted summand and zero on the shifted summand.
Tensor this map with P. K-flatness preserves its quasi-isomorphism. The total-tensor
cone comparison, followed by the unitors, identifies the source with the cone of
scalarOnComplex(d,P)^(n+1), and the single-object tensor comparison identifies the
target with the specified termwise tensor reduction. These comparisons send the
unshifted summand to the quotient unit and kill the shifted summand, giving exactly
the displayed degreewise formula. No choice of a homotopy or a tower comparison is
involved. This includes n=0 (the first positive exponent), P=0 and empty X. -/
theorem internal_principal_cone_level_augmentation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (f : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) f).down s =
        Padic.coefficientExtensionUniformizer l E * f.down s)
    (P : CochainComplex (Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (n : ℕ) :
    ∃ a : CochainComplex.PrincipalCone.level
        (End.of (DerivedNakayama.scalarOnComplex l E X d P)) n ⟶ (level l E X n).obj P,
      QuasiIso a ∧ ∀ q : ℤ, a.f q =
        (CochainComplex.mappingCone.snd
          (End.of (DerivedNakayama.scalarOnComplex l E X d P) ^ (n + 1)).asHom).v
            q q (add_zero q) ≫
            (levelUnit l E X P n).f q := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hd' : d = DerivedNakayama.uniformizerEnd l E := by
    apply End.ext
    apply Mod.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply AddCommGrpCat.hom_ext
    ext f
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    exact (hd S f s).trans (DerivedNakayama.uniformizerEnd_apply l E S f s).symm
  subst d
  let A := Modules l E X
  let e := DerivedNakayama.regularPullbackIso l E X
  let r : DerivedNakayama.UnitScalar.Scalars A :=
    DerivedNakayama.unitEndOnX l E X (DerivedNakayama.uniformizerEnd l E ^ (n + 1))
  have hr : r • 𝟙 (𝟙_ A) = e.inv ≫
      (DerivedNakayama.pullback l E X).map
        (DerivedNakayama.uniformizerEnd l E ^ (n + 1)).asHom ≫ e.hom := by
    rw [DerivedNakayama.UnitScalar.smul_eq, unitEndAction_unit, Category.comp_id]
    rfl
  let S := (ShortComplex.mk
    (DerivedNakayama.uniformizerEnd l E ^ (n + 1)).asHom
    (DerivedNakayama.reductionHom l E (n + 1))
    (DerivedNakayama.reduction_zero l E (n + 1))).map (DerivedNakayama.pullback l E X)
  have hS : S.ShortExact :=
    (DerivedNakayama.pointResolution l E (n + 1)).map_of_exact
      (DerivedNakayama.pullback l E X)
  have hzero : (r • 𝟙 (𝟙_ A)) ≫ finiteUnit l E X n = 0 := by
    rw [hr]
    change (e.inv ≫ S.f ≫ e.hom) ≫ (e.inv ≫ S.g) = 0
    simp only [Category.assoc, Iso.hom_inv_id_assoc, S.zero, comp_zero]
  have hseq : (ShortComplex.mk _ _ hzero).ShortExact := by
    refine ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (S₁ := S) (S₂ := ShortComplex.mk _ _ hzero)
        e e (Iso.refl _) ?_ ?_) hS
    · change e.hom ≫ (r • 𝟙 (𝟙_ A)) = S.f ≫ e.hom
      rw [hr]
      change e.hom ≫ (e.inv ≫ S.f ≫ e.hom) = S.f ≫ e.hom
      rw [Iso.hom_inv_id_assoc]
    · dsimp [finiteUnit, S, e, quotientUnit, DerivedNakayama.reductionHom]
      simp
  have hpow (k : ℕ) : DerivedNakayama.unitEndOnX l E X
      (DerivedNakayama.uniformizerEnd l E ^ k) =
      DerivedNakayama.unitEndOnX l E X (DerivedNakayama.uniformizerEnd l E) ^ k := by
    apply End.ext
    exact conjugateFunctor_pow (DerivedNakayama.pullback l E X) e
      (DerivedNakayama.uniformizerEnd l E) k
  let μ : End P := .of (DerivedNakayama.scalarOnComplex l E X
    (DerivedNakayama.uniformizerEnd l E) P)
  have hbase (q : ℤ) : μ.asHom.f q = (unitEndAction (P.X q)
      (DerivedNakayama.unitEndOnX l E X (DerivedNakayama.uniformizerEnd l E))).asHom := by
    change (DerivedNakayama.scalarOnComplex l E X
      (DerivedNakayama.uniformizerEnd l E) P).f q = _
    rw [DerivedNakayama.scalarOnComplex_eq]
    change DerivedNakayama.unitEndOnX l E X
      (DerivedNakayama.uniformizerEnd l E) • 𝟙 (P.X q) = _
    rw [DerivedNakayama.UnitScalar.smul_eq, Category.comp_id]
  have hμ : (μ ^ (n + 1)).asHom = r • 𝟙 P := by
    apply HomologicalComplex.hom_ext
    intro q
    rw [complexAction_pow P μ _ hbase, ← hpow]
    change (unitEndAction (P.X q) r).asHom = r • 𝟙 (P.X q)
    rw [DerivedNakayama.UnitScalar.smul_eq, Category.comp_id]
  change ∃ a : CochainComplex.mappingCone (μ ^ (n + 1)).asHom ⟶ (level l E X n).obj P,
    QuasiIso a ∧ ∀ q : ℤ, a.f q =
      (CochainComplex.mappingCone.snd (μ ^ (n + 1)).asHom).v q q (add_zero q) ≫
        (levelUnit l E X P n).f q
  rw [hμ]
  exact normalized_scalar_augmentation r (finiteUnit l E X n) hzero hseq P hP

end AlgebraicGeometry.ProEtale.AdicCompletion
