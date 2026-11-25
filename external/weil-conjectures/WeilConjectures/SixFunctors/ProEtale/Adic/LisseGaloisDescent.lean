/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGerm
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint

/-!
# Galois descent for sections of lisse sheaves over fields

Let `k : Spec K' ⟶ Y` be a weakly étale morphism from the spectrum of a field and `Ω / K'` a
separable normal (Galois, possibly infinite) extension. Then `Spec Ω ⟶ Spec K' ⟶ Y` is an
object of `Y_proét` on which `Gal(Ω / K')` acts by the automorphisms `Spec σ`
(`AlgebraicGeometry.ProEtale.fieldExtAut`), and `Spec Ω ⟶ Spec K'` is a pro-étale cover. For a
lisse `ℓ`-adic sheaf `F` on `Y`, restriction identifies the sections of `F` over `Spec K'` with
the `Gal(Ω / K')`-invariant sections over `Spec Ω`:

* restriction is injective
  (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.injective_map_fieldExtHom`): every geometric point
  of `Spec K'` lifts to `Spec Ω`, and sections of lisse sheaves are detected by their germs;
* an invariant section descends
  (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_map_fieldExtHom_eq`): by the sheaf
  condition for the cover `Spec Ω ⟶ Spec K'` it suffices that its pullbacks along any two
  `p₁ p₂ : Z ⟶ Spec Ω` over `Spec K'` agree, which is checked on germs, since any two
  `K'`-embeddings of the normal extension `Ω` into an algebraically closed field differ by an
  element of `Gal(Ω / K')` (`AlgebraicGeometry.ProEtale.exists_algEquiv_comp_specMap_eq`).

For `K'` the fraction field of the strict henselization of a curve at a boundary point and `Ω` a
separable closure, `Gal(Ω / K')` is the inertia group at the point: this is the second step of
blueprint `lemma-boundary-stalk--1`, which identifies the boundary stalk of `j_* F`
with the inertia invariants of the geometric generic stalk.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {K' Ω : Type u} [Field K'] [Field Ω] [Algebra K' Ω]

variable (K' Ω) in
/-- The morphism `Spec Ω ⟶ Spec K'` of a field extension. -/
noncomputable abbrev specFieldMap : Spec (.of Ω) ⟶ Spec (.of K') :=
  Spec.map (CommRingCat.ofHom (algebraMap K' Ω))

/-- `Spec σ` lies over `Spec K'` for `σ ∈ Gal(Ω / K')`. -/
lemma specMap_algEquiv_comp_specFieldMap (σ : Ω ≃ₐ[K'] Ω) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ specFieldMap K' Ω = specFieldMap K' Ω := by
  rw [← Spec.map_comp]
  congr 2
  ext x
  simp

/-- **Embeddings of a normal extension differ by an automorphism.** Two morphisms
`Spec L ⟶ Spec Ω` over `Spec K'`, for `Ω / K'` normal, differ by `Spec σ` for some
`σ ∈ Gal(Ω / K')`. -/
lemma exists_algEquiv_comp_specMap_eq [Normal K' Ω] {L : Type u} [Field L]
    (y₁ y₂ : Spec (.of L) ⟶ Spec (.of Ω))
    (h : y₁ ≫ specFieldMap K' Ω = y₂ ≫ specFieldMap K' Ω) :
    ∃ σ : Ω ≃ₐ[K'] Ω, y₂ = y₁ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  obtain ⟨φ₁, rfl⟩ : ∃ φ, Spec.map φ = y₁ := ⟨_, Spec.map_preimage y₁⟩
  obtain ⟨φ₂, rfl⟩ : ∃ φ, Spec.map φ = y₂ := ⟨_, Spec.map_preimage y₂⟩
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
  have h' (x : K') : φ₁.hom (algebraMap K' Ω x) = φ₂.hom (algebraMap K' Ω x) :=
    congrArg (fun φ : CommRingCat.of K' ⟶ CommRingCat.of L ↦ φ.hom x) h
  let : Algebra K' L := (φ₁.hom.comp (algebraMap K' Ω)).toAlgebra
  let a : Ω →ₐ[K'] L := { φ₁.hom with commutes' := fun _ ↦ rfl }
  let b : Ω →ₐ[K'] L := { φ₂.hom with commutes' := fun x ↦ (h' x).symm }
  let : Algebra Ω L := a.toRingHom.toAlgebra
  have : IsScalarTower K' Ω L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let σ := b.restrictNormal' Ω
  refine ⟨σ, ?_⟩
  rw [← Spec.map_comp, Spec.map_inj]
  ext x
  exact (b.restrictNormal_commutes Ω x).symm

variable [Algebra.IsSeparable K' Ω] {Y : Scheme.{u}} (k : Spec (.of K') ⟶ Y) [WeaklyEtale k]

instance : WeaklyEtale (specFieldMap K' Ω) := by
  have := Algebra.IndEtale.of_isSeparable K' Ω
  infer_instance

variable (Ω) in
/-- The object `Spec Ω ⟶ Spec K' ⟶ Y` of `Y_proét`. -/
noncomputable def fieldExtObj : Y.ProEt :=
  ProEt.mk (specFieldMap K' Ω ≫ k)

variable (Ω) in
/-- The morphism `Spec Ω ⟶ Spec K'` of `Y_proét`. -/
noncomputable def fieldExtHom : fieldExtObj Ω k ⟶ ProEt.mk k :=
  MorphismProperty.Over.homMk (specFieldMap K' Ω) rfl

/-- The action of `σ ∈ Gal(Ω / K')` on `Spec Ω ⟶ Spec K' ⟶ Y` by `Spec σ`. -/
noncomputable def fieldExtAut (σ : Ω ≃ₐ[K'] Ω) : fieldExtObj Ω k ⟶ fieldExtObj Ω k :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    change _ ≫ specFieldMap K' Ω ≫ k = specFieldMap K' Ω ≫ k
    rw [← Category.assoc, specMap_algEquiv_comp_specFieldMap])

lemma fieldExtAut_comp_fieldExtHom (σ : Ω ≃ₐ[K'] Ω) :
    fieldExtAut k σ ≫ fieldExtHom Ω k = fieldExtHom Ω k :=
  MorphismProperty.Over.Hom.ext (specMap_algEquiv_comp_specFieldMap σ)

variable {l : ℕ} [Fact l.Prime] {F : AdicSheaf l Y}

/-- The restriction of a section over `Spec K'` to `Spec Ω` is `Gal(Ω / K')`-invariant. -/
lemma map_fieldExtAut_map_fieldExtHom (σ : Ω ≃ₐ[K'] Ω)
    (s : ToType (F.X.obj.obj (op (ProEt.mk k)))) :
    F.X.obj.map (fieldExtAut k σ).op (F.X.obj.map (fieldExtHom Ω k).op s) =
      F.X.obj.map (fieldExtHom Ω k).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    fieldExtAut_comp_fieldExtHom]

/-- **Restriction to `Spec Ω` is injective** on sections of a lisse sheaf over `Spec K'`. -/
theorem IsAdicLisseSheaf.injective_map_fieldExtHom (hF : IsAdicLisseSheaf F) :
    Function.Injective (F.X.obj.map (fieldExtHom Ω k).op) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ hF.eq_zero_of_germ_eq_zero s
    fun K _ _ w t ↦ ?_
  -- lift the point `Spec K ⟶ Spec K'` of `t` to `Spec Ω`
  obtain ⟨ψ, hψu⟩ : ∃ ψ, Spec.map ψ = t.left ≫ pullback.fst k (w ≫ k) :=
    ⟨_, Spec.map_preimage _⟩
  let : Algebra K' K := ψ.hom.toAlgebra
  have := Algebra.IsSeparable.isAlgebraic K' Ω
  let ψ' : Ω →ₐ[K'] K := IsAlgClosed.lift
  have hψ' : Spec.map (CommRingCat.ofHom ψ'.toRingHom) ≫ specFieldMap K' Ω = Spec.map ψ := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact ψ'.commutes x
  have ht₂ : t.left ≫ pullback.snd k (w ≫ k) = 𝟙 _ := MorphismProperty.Over.w t
  have hc : (Spec.map (CommRingCat.ofHom ψ'.toRingHom)) ≫ specFieldMap K' Ω ≫ k =
      𝟙 _ ≫ w ≫ k := by
    rw [← Category.assoc, hψ', hψu, Category.assoc, pullback.condition, ← Category.assoc, ht₂]
    exact Category.id_comp _
  let t' : ProEt.mk (𝟙 (Spec (.of K))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (w ≫ k)).obj (fieldExtObj Ω k) :=
    MorphismProperty.Over.homMk (pullback.lift _ _ hc) (pullback.lift_snd _ _ _)
  have ht' : t' ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (w ≫ k)).map
      (fieldExtHom Ω k) = t := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change pullback.lift _ _ hc ≫ pullback.lift (pullback.fst _ (w ≫ k) ≫ specFieldMap K' Ω)
        (pullback.snd _ (w ≫ k)) _ ≫ pullback.fst k (w ≫ k) = _
      rw [pullback.lift_fst, pullback.lift_fst_assoc, hψ', hψu]
      rfl
    · change pullback.lift _ _ hc ≫ pullback.lift (pullback.fst _ (w ≫ k) ≫ specFieldMap K' Ω)
        (pullback.snd _ (w ≫ k)) _ ≫ pullback.snd k (w ≫ k) = _
      rw [pullback.lift_snd, pullback.lift_snd]
      exact ht₂.symm
  rw [← map_germ (fieldExtHom Ω k) t t' ht', ConcreteCategory.comp_apply, hs, map_zero]

/-- Germs of a `Gal(Ω / K')`-invariant section over `Spec Ω` at two lifts of the same point of
`Spec K'` agree. -/
lemma germ_eq_of_forall_map_fieldExtAut_eq [Normal K' Ω]
    (v : ToType (F.X.obj.obj (op (fieldExtObj Ω k))))
    (hv : ∀ σ : Ω ≃ₐ[K'] Ω, F.X.obj.map (fieldExtAut k σ).op v = v)
    {K : Type u} [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ Y)
    (T₁ T₂ : ProEt.mk (𝟙 (Spec (.of K))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj (fieldExtObj Ω k))
    (hT : (T₁.left ≫ pullback.fst _ g) ≫ specFieldMap K' Ω =
      (T₂.left ≫ pullback.fst _ g) ≫ specFieldMap K' Ω) :
    germ _ g F.X T₁ v = germ _ g F.X T₂ v := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp_specMap_eq _ _ hT
  have hT' : T₁ ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map (fieldExtAut k σ) =
      T₂ := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change T₁.left ≫ pullback.lift
        (pullback.fst _ g ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
        (pullback.snd _ g) _ ≫ pullback.fst _ g = _
      rw [pullback.lift_fst, ← Category.assoc, ← hσ]
    · change T₁.left ≫ pullback.lift
        (pullback.fst _ g ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
        (pullback.snd _ g) _ ≫ pullback.snd _ g = _
      rw [pullback.lift_snd]
      exact (MorphismProperty.Over.w T₁).trans (MorphismProperty.Over.w T₂).symm
  rw [← hT', ← map_germ (fieldExtAut k σ) _ T₁ rfl, ConcreteCategory.comp_apply, hv]

/-- **Galois descent.** A `Gal(Ω / K')`-invariant section over `Spec Ω` of a lisse sheaf is the
restriction of a section over `Spec K'`. -/
theorem IsAdicLisseSheaf.exists_map_fieldExtHom_eq [Normal K' Ω] (hF : IsAdicLisseSheaf F)
    (v : ToType (F.X.obj.obj (op (fieldExtObj Ω k))))
    (hv : ∀ σ : Ω ≃ₐ[K'] Ω, F.X.obj.map (fieldExtAut k σ).op v = v) :
    ∃ s, F.X.obj.map (fieldExtHom Ω k).op s = v := by
  have hS : Presieve.IsSheaf (ProEt.topology Y)
      (F.X.obj ⋙ CategoryTheory.forget (WeilCoefficients.{u} l)) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose _ (CategoryTheory.forget (WeilCoefficients.{u} l))).obj F.X).property
  have hcov : Sieve.generate (Presieve.singleton (fieldExtHom Ω k)) ∈
      ProEt.topology Y (ProEt.mk k) := by
    rw [ProEt.mem_topology_iff]
    refine ⟨Presieve.singleton (fieldExtHom Ω k), ?_, Sieve.le_generate _⟩
    rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
    have : Surjective (specFieldMap K' Ω) :=
      ⟨fun x ↦ ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale)
      (f := specFieldMap K' Ω) inferInstance
  have hsf := (Presieve.isSheafFor_iff_generate _).2 (hS _ hcov)
  obtain ⟨s, hs, -⟩ := Presieve.isSheafFor_singleton.1 hsf v fun {Z} p₁ p₂ hp ↦ by
    change F.X.obj.map p₁.op v = F.X.obj.map p₂.op v
    rw [← sub_eq_zero]
    refine hF.eq_zero_of_germ_eq_zero _ fun K _ _ w t ↦ ?_
    rw [map_sub, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      map_germ p₁ _ t rfl, map_germ p₂ _ t rfl, sub_eq_zero]
    refine germ_eq_of_forall_map_fieldExtAut_eq k v hv _ _ _ ?_
    have hp' : p₁.left ≫ specFieldMap K' Ω = p₂.left ≫ specFieldMap K' Ω :=
      congrArg (fun f ↦ f.left) hp
    change (t.left ≫ pullback.lift (pullback.fst _ (w ≫ Z.hom) ≫ p₁.left)
        (pullback.snd _ (w ≫ Z.hom)) _ ≫ pullback.fst _ (w ≫ Z.hom)) ≫ specFieldMap K' Ω =
      (t.left ≫ pullback.lift (pullback.fst _ (w ≫ Z.hom) ≫ p₂.left)
        (pullback.snd _ (w ≫ Z.hom)) _ ≫ pullback.fst _ (w ≫ Z.hom)) ≫ specFieldMap K' Ω
    rw [pullback.lift_fst, pullback.lift_fst, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, hp']
  exact ⟨s, hs⟩

end AlgebraicGeometry.ProEtale
