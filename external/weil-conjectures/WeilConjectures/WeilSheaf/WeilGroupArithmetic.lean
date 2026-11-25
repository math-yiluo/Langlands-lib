/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Extension
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantExtension
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroupDense
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
public import WeilConjectures.WeilSheaf.WeilMonodromyGeneral

/-!
# The Weil group inside the arithmetic fundamental group

Let `X₀` be a scheme over a finite field `K` with geometric fibre `p : X ⟶ X₀`, and let
`B = (t, β)` be base point data (`AlgebraicGeometry.FrobeniusBasePoint`): a geometric point `t`
of `X` and a path `β : F_t ≅ F_{t ≫ Fr}`. The Weil group `W = π₁(X, t) ⋊ ℤ` of `B` maps to the
arithmetic fundamental group `π₁(X₀, t ≫ p) = Aut F_{t ≫ p}`
(`AlgebraicGeometry.FrobeniusBasePoint.arithHom`): a loop `g` at `t` goes to the induced path
`p_* g` (`AlgebraicGeometry.FrobeniusBasePoint.geomAut`), and the generator `γ` of `ℤ` to the
push-down `F₀ = p_* β` of the path `β` (`AlgebraicGeometry.FrobeniusBasePoint.frobAut`), using
`Fr ≫ p = p`.

For a `K̄`-rational `t` and `X₀` geometrically connected, quasi-compact, quasi-separated and of
finite type, this realises `W` as the Weil group `W(X₀, t ≫ p) ⊆ π₁(X₀) × ℤ` of Deligne (Weil II,
1.1.7): `F₀` acts on the constant covers as the geometric Frobenius, so `arithHom` lands in the
Weil group with the right degree (`AlgebraicGeometry.FrobeniusBasePoint.mem_weilGroup_arithHom`);
`arithHom` is injective on `π₁(X, t)` (the homotopy exact sequence, SGA 1 IX.6.1, Stacks `0BTX`),
has dense range (`AlgebraicGeometry.FrobeniusBasePoint.denseRange_arithHom`), and detects degrees
modulo every `m` through the constant cover of degree `m`
(`AlgebraicGeometry.FrobeniusBasePoint.exists_isOpen_dvd_deg`). These are the hypotheses of
`Representation.exists_continuous_extension_of_isBoundedOn`.

The proofs follow the curve case (`AlgebraicGeometry.WeilGroup.BasePointData`), where the
curve hypothesis only enters through the structure `AlgebraicGeometry.WeilGroup`.
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.FrobeniusBasePoint

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  (B : FrobeniusBasePoint K X)

section Lift

variable {H : Type*} [Group H] (φ : Aut (fiber B.t) →* H) (F : H)
  (hφ : ∀ g, φ (B.frobConj g) = F⁻¹ * φ g * F)

include hφ in
/-- If `φ` carries the Frobenius transport of loops to conjugation by `F⁻¹`, it carries the
action of `n ∈ ℤ` defining `π₁(X, t) ⋊ ℤ` to conjugation by `Fⁿ`. -/
lemma map_frobAction (n : ℤ) (x : Aut (fiber B.t)) :
    φ (B.frobAction (Multiplicative.ofAdd n) x) = F ^ n * φ x * (F ^ n)⁻¹ := by
  have hφ' (x : Aut (fiber B.t)) : φ (B.frobConj.symm x) = F * φ x * F⁻¹ := by
    have h := hφ (B.frobConj.symm x)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    group
  simp only [frobAction, zpowersHom_apply, toAdd_ofAdd]
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, MulAut.mul_apply, ih, MulAut.inv_apply, hφ']
    group
  | pred n ih =>
    rw [zpow_sub_one, MulAut.mul_apply, ih, inv_inv, hφ]
    group

/-- The homomorphism `π₁(X, t) ⋊ ℤ →* H`, `(g, n) ↦ φ(g) Fⁿ`, attached to `φ : π₁(X, t) →* H`
and `F ∈ H` such that `φ(β ≫ Fr_* g ≫ β⁻¹) = F⁻¹ φ(g) F`. -/
noncomputable def weilGroupLift : B.WeilGroup →* H :=
  SemidirectProduct.lift φ (zpowersHom H F) fun g ↦ by
    ext x
    have h := B.map_frobAction φ F hφ (Multiplicative.toAdd g) x
    rw [ofAdd_toAdd] at h
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      zpowersHom_apply]
    exact h

@[simp]
lemma weilGroupLift_inl (g : Aut (fiber B.t)) :
    B.weilGroupLift φ F hφ (SemidirectProduct.inl g) = φ g :=
  SemidirectProduct.lift_inl _ _ _ g

@[simp]
lemma weilGroupLift_inr (n : Multiplicative ℤ) :
    B.weilGroupLift φ F hφ (SemidirectProduct.inr n) = F ^ n.toAdd :=
  SemidirectProduct.lift_inr _ _ _ n

end Lift

/-- The map `π₁(X, t) → π₁(X₀, t ≫ p)` induced by base change of finite étale schemes along the
projection `p : X ⟶ X₀` of the geometric fibre. -/
noncomputable def geomAut :
    Aut (fiber B.t) →* Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) :=
  pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t

lemma geomAut_apply (g : Aut (fiber B.t)) :
    B.geomAut g = .of (pullbackPathIso (X ↘ Spec (.of K)).geometricFiberProj g.asIso) :=
  rfl

/-- The push-down `F₀ ∈ π₁(X₀, t ≫ p)` of the path `β : F_t ≅ F_{t ≫ Fr}`, using
`t ≫ Fr ≫ p = t ≫ p`: a lift of the geometric Frobenius
(`AlgebraicGeometry.FrobeniusBasePoint.mem_weilGroup_frobAut`). -/
noncomputable def frobAut : Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) :=
  .of (pullbackPathIso (X ↘ Spec (.of K)).geometricFiberProj B.frobPath ≪≫
    eqToIso (congrArg fiber (by
      rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj])))

/-- Conjugation by `F₀` is the Frobenius transport of loops at `t`:
`p_*(β ≫ Fr_* g ≫ β⁻¹) = F₀⁻¹ p_*(g) F₀`. -/
theorem geomAut_frobConj (g : Aut (fiber B.t)) :
    B.geomAut (B.frobConj g) = B.frobAut⁻¹ * B.geomAut g * B.frobAut := by
  apply Aut.ext
  simp only [geomAut_apply, frobAut, frobConj_apply, Aut.mul_asIso, Aut.inv_asIso]
  rw [pullbackPathIso_trans, pullbackPathIso_trans, pullbackPathIso_symm,
    pullbackPathIso_pullbackPathIso_of_comp_eq
      (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)]
  simp only [Iso.trans_symm, eqToIso_symm', Iso.trans_assoc]

/-- **The Weil group in the arithmetic fundamental group**: `(g, n) ↦ p_*(g) F₀ⁿ`. -/
noncomputable def arithHom :
    B.WeilGroup →* Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) :=
  B.weilGroupLift B.geomAut B.frobAut B.geomAut_frobConj

@[simp]
lemma arithHom_inl (g : Aut (fiber B.t)) :
    B.arithHom (SemidirectProduct.inl g) = B.geomAut g :=
  weilGroupLift_inl _ _ _ _ g

@[simp]
lemma arithHom_inr (n : Multiplicative ℤ) :
    B.arithHom (SemidirectProduct.inr n) = B.frobAut ^ n.toAdd :=
  weilGroupLift_inr _ _ _ _ n

/-- The map `π₁(X, t) → π₁(X₀, t ≫ p)` is continuous. -/
lemma continuous_geomAut : Continuous B.geomAut :=
  continuous_pullbackPathHom _ _

section WeilGroup

variable [GeometricallyConnected (X ↘ Spec (.of K))] [ConnectedSpace X]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G
    ((fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).obj P)]
  [IsFundamentalGroup (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) G]

/-- **The Frobenius lift has degree one**: for a `K̄`-rational base point, `F₀` acts on the
geometric fibres of the constant covers as the geometric Frobenius. -/
theorem mem_weilGroup_frobAut
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) :
    ((toAutMulEquiv (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) G).symm B.frobAut,
      Multiplicative.ofAdd (1 : ℤ)) ∈
        weilGroup (X ↘ Spec (.of K)) (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) G := by
  refine (mem_weilGroup_iff (X ↘ Spec (.of K)) _ G).2 fun A y ↦ ?_
  simp only [toAdd_ofAdd, zpow_one]
  apply ((ConcreteCategory.isIso_iff_bijective _).1
    (inferInstance : IsIso ((fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).map
      (arithmeticFrobenius (X ↘ Spec (.of K)) A).hom))).1
  rw [fiber_map_arithmeticFrobenius_geometricFrobenius]
  rw [← toAut_hom_app_apply (F := fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) (G := G)]
  rw [← toAutMulEquiv_apply, MulEquiv.apply_symm_apply]
  obtain ⟨z, rfl⟩ : ∃ z : (fiber B.t).obj ((pullback (X ↘ Spec (.of K)).geometricFiberProj).obj
      (constantCover (X ↘ Spec (.of K)) A)),
      (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).hom.app _ z = y :=
    ⟨(pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).inv.app _ y,
      ConcreteCategory.congr_hom ((pullbackFiberIso _ _).inv_hom_id_app _) y⟩
  apply fiber_ext
  rw [fiber_map_left, frobAut, Iso.trans_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    eqToIso_hom_app_left (by
      rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj])]
  simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    pullbackFiberIso_hom_app_left]
  rw [show (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).inv.app _
      ((pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).hom.app _ z) = z from
    ConcreteCategory.congr_hom ((pullbackFiberIso _ _).hom_inv_id_app _) z]
  erw [path_section B.frobPath _ _ (sectionOfPoint_snd (X ↘ Spec (.of K)) A _ _) z
    (left_eq_sectionOfPoint (X ↘ Spec (.of K)) ht A z)]
  conv_rhs => rw [left_eq_sectionOfPoint (X ↘ Spec (.of K)) ht A z]
  apply Limits.pullback.hom_ext
  · simp [-constantCover_obj_hom, arithmeticFrobenius, constantCoverIso]
  · have key := comp_specMap_frobenius A (pointOfFiber (X ↘ Spec (.of K)) A z)
    simp only [pointOfFiber, Category.assoc] at key
    simp [-constantCover_obj_hom, arithmeticFrobenius, constantCoverIso, key]

omit [GeometricallyConnected (X ↘ Spec (CommRingCat.of K))] in
/-- `geomAut` is the map of fundamental groups induced by the base change isomorphism
`F_t ∘ p^* ≅ F_{t ≫ p}`, for any (small) fundamental group `G'` of the fibre functor at `t`. -/
lemma geomAut_eq_fundamentalGroupMap [ConnectedSpace (X ↘ Spec (.of K)).geometricFiber]
    (G' : Type u) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
    [∀ P, MulAction G' ((fiber B.t).obj P)] [IsFundamentalGroup (fiber B.t) G']
    (g : Aut (fiber B.t)) :
    B.geomAut g = toAutMulEquiv (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) G
      (fundamentalGroupMap (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t) G' G
        ((toAutMulEquiv (fiber B.t) G').symm g)) := by
  ext P y
  obtain ⟨y', rfl⟩ : ∃ y', (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).hom.app P
      y' = y :=
    ⟨(pullbackFiberIso _ B.t).inv.app P y,
      ConcreteCategory.congr_hom ((pullbackFiberIso _ B.t).inv_hom_id_app P) y⟩
  have hg (x : (fiber B.t).obj ((pullback (X ↘ Spec (.of K)).geometricFiberProj).obj P)) :
      (toAutMulEquiv (fiber B.t) G').symm g • x = g.asIso.hom.app _ x := by
    rw [← toAut_hom_app_apply, ← toAutMulEquiv_apply, MulEquiv.apply_symm_apply]
  rw [toAutMulEquiv_apply, toAut_hom_app_apply, fundamentalGroupMap_smul, hg, geomAut_apply]
  simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id_app_assoc]
  exact ConcreteCategory.comp_apply _ _ _

/-- The image of `π₁(X, t)` in `π₁(X₀, t ≫ p)` acts trivially on the constant covers, for a
`K̄`-rational base point. -/
theorem mem_weilGroup_geomAut [ConnectedSpace (X ↘ Spec (.of K)).geometricFiber]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _)
    (g : Aut (fiber B.t)) :
    ((toAutMulEquiv (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) G).symm (B.geomAut g),
      (1 : Multiplicative ℤ)) ∈
        weilGroup (X ↘ Spec (.of K)) (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) G := by
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  rw [B.geomAut_eq_fundamentalGroupMap G G', MulEquiv.symm_apply_apply]
  exact mem_weilGroup_fundamentalGroupMap _ ht _ G G' _

/-- **The Weil group in the arithmetic fundamental group**: for a `K̄`-rational base point, the
image of `w ∈ π₁(X, t) ⋊ ℤ` lies in the Weil group `W(X₀, t ≫ p) ⊆ π₁(X₀) × ℤ`, with degree the
`ℤ`-component of `w`. -/
theorem mem_weilGroup_arithHom [ConnectedSpace (X ↘ Spec (.of K)).geometricFiber]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) (w : B.WeilGroup) :
    ((toAutMulEquiv (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) G).symm
        (B.arithHom w), SemidirectProduct.rightHom w) ∈
        weilGroup (X ↘ Spec (.of K)) (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) G := by
  set e := toAutMulEquiv (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) G
  obtain ⟨g, n, rfl⟩ :
      ∃ g n, w = (SemidirectProduct.inl g : B.WeilGroup) * SemidirectProduct.inr n :=
    ⟨w.left, w.right, (SemidirectProduct.inl_left_mul_inr_right w).symm⟩
  set w : B.WeilGroup := SemidirectProduct.inl g * SemidirectProduct.inr n with hw
  have h : ((e.symm (B.arithHom w), SemidirectProduct.rightHom w) :
        G × Multiplicative ℤ) = (e.symm (B.geomAut g), 1) *
          (e.symm B.frobAut, Multiplicative.ofAdd (1 : ℤ)) ^ (Multiplicative.toAdd n) := by
    rw [map_mul, map_mul, arithHom_inl, arithHom_inr, map_mul, map_zpow,
      SemidirectProduct.rightHom_inl, SemidirectProduct.rightHom_inr, Prod.pow_mk, Prod.mk_mul_mk,
      one_mul, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd, one_mul]
  rw [h]
  exact mul_mem (B.mem_weilGroup_geomAut G ht _)
    (zpow_mem (B.mem_weilGroup_frobAut G ht) _)

end WeilGroup

omit [Finite K] in
/-- The geometric fibre of a geometrically connected scheme is connected. -/
lemma connectedSpace_geometricFiber [GeometricallyConnected (X ↘ Spec (.of K))] :
    ConnectedSpace (X ↘ Spec (.of K)).geometricFiber :=
  GeometricallyConnected.geometrically_connectedSpace (f := X ↘ Spec (.of K))
    (Scheme.specAlgebraicClosure K).hom (X ↘ Spec (.of K)).geometricFiberProj
    (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)

omit [Finite K] in
/-- The geometric fibre of the constant cover `X₀ ×_K Spec L` attached to a finite extension
`L / K` is nonempty at a geometric point with values in an algebraically closed field: it is the
set of `K`-embeddings of `L`. -/
lemma nonempty_fiber_constantCover {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K)) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X₀) (L : Type u) [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.Etale K L] :
    Nonempty ((fiber s).obj (constantCover p (FiniteEtaleAlgebra.of L))) := by
  let : Algebra K Ω := (baseRingHom p s).toAlgebra
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let ψ : L →ₐ[K] Ω := IsAlgClosed.lift
  exact ⟨(fiberConstantCoverEquiv p s _).symm ⟨ψ.toRingHom, RingHom.ext fun k ↦ ψ.commutes k⟩⟩

section Exact

variable [GeometricallyConnected (X ↘ Spec (.of K))] [ConnectedSpace X] [CompactSpace X]
  [QuasiSeparatedSpace X]

/-- **The map `π₁(X, t) → π₁(X₀, t ≫ p)` is injective** (the homotopy exact sequence, SGA 1
IX.6.1): every finite étale scheme over the geometric fibre embeds into the base change of a
finite étale `X₀`-scheme. -/
theorem geomAut_injective : Function.Injective B.geomAut := by
  have := connectedSpace_geometricFiber (K := K) (X := X)
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
  intro g g' h
  rw [B.geomAut_eq_fundamentalGroupMap G G', B.geomAut_eq_fundamentalGroupMap G G'] at h
  exact (toAutMulEquiv (fiber B.t) G').symm.injective
    (fundamentalGroupMap_injective_geometricFiber _ _ G' G ((toAutMulEquiv _ G).injective h))

/-- **The Weil group is dense in `π₁(X₀, t ≫ p)`**, for a `K̄`-rational base point and `X₀` of
finite type: the image of `arithHom` is the projection of the Weil group `W(X₀) ⊆ π₁(X₀) × ℤ`
(exactness of the homotopy sequence in the middle,
`AlgebraicGeometry.Scheme.FiniteEtale.mem_range_fundamentalGroupMap_of_mem_weilGroup`), which is
dense (`AlgebraicGeometry.Scheme.FiniteEtale.eq_top_of_forall_mem_weilGroup`). -/
theorem denseRange_arithHom [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) :
    DenseRange B.arithHom := by
  have := connectedSpace_geometricFiber (K := K) (X := X)
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
  set e := toAutMulEquiv (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) G
  have he : Continuous e := (toAutHomeo _ G).continuous
  set H : Subgroup G := B.arithHom.range.topologicalClosure.comap e.toMonoidHom
  have hH : IsClosed (H : Set G) :=
    B.arithHom.range.isClosed_topologicalClosure.preimage he
  have htop := eq_top_of_forall_mem_weilGroup (X ↘ Spec (.of K)) G H hH fun w hw ↦ by
    -- `w = (g, n)` with `g F₀⁻ⁿ` in the image of `π₁(X, t)`
    obtain ⟨g, n⟩ := w
    have hF := B.mem_weilGroup_frobAut G ht
    have h₁ : (g * (e.symm B.frobAut) ^ (-Multiplicative.toAdd n), (1 : Multiplicative ℤ)) ∈
        weilGroup (X ↘ Spec (.of K)) (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) G := by
      have := mul_mem hw (zpow_mem hF (-Multiplicative.toAdd n))
      rwa [Prod.pow_mk, Prod.mk_mul_mk, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_neg,
        ofAdd_toAdd, mul_inv_cancel] at this
    obtain ⟨k, hk⟩ := mem_range_fundamentalGroupMap_of_mem_weilGroup _
      (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t) G' G _ h₁
    refine B.arithHom.range.le_topologicalClosure
      ⟨SemidirectProduct.inl (toAutMulEquiv (fiber B.t) G' k) * SemidirectProduct.inr n, ?_⟩
    rw [map_mul, arithHom_inl, arithHom_inr, B.geomAut_eq_fundamentalGroupMap G G',
      MulEquiv.symm_apply_apply, hk]
    rw [map_mul, map_zpow, MulEquiv.apply_symm_apply, zpow_neg, inv_mul_cancel_right]
    rfl
  intro x
  have hx : e (e.symm x) ∈ B.arithHom.range.topologicalClosure := by
    have : e.symm x ∈ H := htop ▸ Subgroup.mem_top _
    exact this
  rw [MulEquiv.apply_symm_apply, ← SetLike.mem_coe, Subgroup.topologicalClosure_coe,
    MonoidHom.coe_range] at hx
  exact hx

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- **`arithHom` detects the degree modulo `m`**: the stabiliser of a point of the geometric
fibre of the constant cover `X₀ ×_K Spec L`, `[L : K] = m`, is an open subgroup of
`π₁(X₀, t ≫ p)`, and an element `w` of the Weil group mapping into it has `m ∣ deg w`, since
`arithHom w` acts there as the `deg w`-th power of the geometric Frobenius, of order `m`. -/
theorem exists_isOpen_dvd_deg
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) (m : ℕ)
    (hm : 0 < m) :
    ∃ O : Set (Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))), IsOpen O ∧ 1 ∈ O ∧
      ∀ w, B.arithHom w ∈ O → (m : ℤ) ∣ Multiplicative.toAdd (SemidirectProduct.rightHom w) := by
  have := connectedSpace_geometricFiber (K := K) (X := X)
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
  -- a field extension `L / K` of degree `m` inside `K̄`
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have : NeZero m := ⟨hm.ne'⟩
  let φ : FiniteField.Extension K (ringChar K) m →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  set L := φ.fieldRange
  let eL := AlgEquiv.ofInjectiveField φ
  have : Module.Finite K L := Module.Finite.equiv eL.toLinearEquiv
  have hL : Module.finrank K L = m :=
    eL.toLinearEquiv.finrank_eq.symm.trans (FiniteField.finrank_extension K _ m)
  have : Algebra.Etale K L :=
    ⟨Algebra.FormallyEtale.of_isSeparable K L, Algebra.FinitePresentation.of_finiteType.1
      inferInstance⟩
  -- a point of the geometric fibre of the constant cover
  obtain ⟨z⟩ : Nonempty ((fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).obj
      (constantCover (X ↘ Spec (.of K)) (FiniteEtaleAlgebra.of L))) := by
    exact nonempty_fiber_constantCover _ _ L
  refine ⟨{σ | σ • z = z}, ?_, one_smul _ z, fun w hw ↦ ?_⟩
  · exact (isOpen_discrete {z}).preimage (continuous_id.smul continuous_const)
  have h := (mem_weilGroup_iff _ _ G).1 (B.mem_weilGroup_arithHom G ht w)
    (FiniteEtaleAlgebra.of L) z
  have h₂ : (toAutMulEquiv (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) G).symm
      (B.arithHom w) • z = z := by
    rw [← toAut_hom_app_apply, ← toAutMulEquiv_apply, MulEquiv.apply_symm_apply]
    exact hw
  rw [← hL]
  exact dvd_of_geometricFrobenius_zpow_apply _ _ L z _ (h.symm.trans h₂)

end Exact

end AlgebraicGeometry.FrobeniusBasePoint
