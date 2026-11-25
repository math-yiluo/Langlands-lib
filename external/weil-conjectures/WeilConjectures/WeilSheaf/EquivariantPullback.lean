/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CurvePullback
public import WeilConjectures.WeilSheaf.StalkComparison

/-!
# Stalks of Weil sheaves pulled back to a scheme over a finite extension

Let `j : Ȳ ⟶ X̄` intertwine `Fr^N` and `Fr_Y`, with `N = [L : k₀]`, and let
`AlgebraicGeometry.WeilSheaf.curvePullback j hj` be the induced pullback of Weil sheaves on `X`
over `k₀` to Weil sheaves on `Y` over `L`. This file compares stalks.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_equiv_stalkAt_curvePullback`: the stalk of the pullback at a
  geometric point `s'` of `Ȳ`, with its Frobenius relative to `L_n`, is the stalk of `F` at the
  corresponding geometric point of `X̄` with its Frobenius relative to `𝔽_{q^{N n}}`.
- `AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_curvePullback_of_iSup_eq_top`: purity of
  the pullback from purity of the pullbacks of spanning subsheaves defined over `L`.
- `AlgebraicGeometry.WeilSheaf.IsReal.curvePullback`: the pullback of an `ι`-real sheaf is
  `ι`-real.
-/

@[expose] public section

-- The Weil sheaf stalks and the `ℓ`-adic pullbacks used here are elaborated without these
-- instances; elaborating the statements through them would produce terms which the kernel
-- compares slowly with the imported ones.
attribute [-instance] ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier
  ModuleCat.isGrothendieckAbelian_of_commRing
  CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {l : ℕ} [Fact l.Prime]

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {L : Type u} [Field L] [Finite L] [Fact (ringChar L ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of L))] {N : ℕ}
  (j : (Y ↘ Spec (CommRingCat.of L)).geometricFiber ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (hj : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
    (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ j)

/-- If finitely many subsheaves defined over `L` span `F̄` and the pullback of each is punctually
`ι`-pure of weight `w`, so is the pullback of `F`: it is a quotient of their direct sum. -/
theorem isPunctuallyPureOfWeight_curvePullback_of_iSup_eq_top
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of L))] (F : WeilSheaf k₀ l X) {M : ℕ}
    (Q : Fin M → Subobject F.obj.carrier) (hQ : (Finset.univ : Finset (Fin M)).sup Q = ⊤)
    (hQN : ∀ n, (⇑F.frobeniusTwist)^[N] (Q n) = Q n)
    (hQl : ∀ n, IsAdicLisseSheaf (Subobject.underlying.obj (Q n))) {ι : PadicAlgCl l →+* ℂ} {w : ℝ}
    (hpure : ∀ n, (curvePullbackSub j hj F (Q n) (hQN n) (hQl n)).IsPunctuallyPureOfWeight ι w) :
    ((curvePullback j hj).obj F).IsPunctuallyPureOfWeight ι w := by
  intro y
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (Y ↘ Spec (CommRingCat.of L)) y
  exact FrobeniusModule.IsPureOfWeight.of_iSup_range_eq_top
    (fun n ↦ stalkAtMap _ _ hs (curvePullbackSubι j hj F (Q n) (hQN n) (hQl n)))
    (fun n ↦ LinearMap.ext fun x ↦ stalkAtMap_frobenius _ _ hs _ x)
    (ProEtale.iSup_range_adicStalkMap_adicUpperStar_eq_top j _ Q hQ) (fun n ↦ hpure n y)

/-- The map induced on the stalks at `s'` by the inclusion `j^* P ⟶ j^* F̄` of the pullback of a
subsheaf, on the global sections of the pullbacks along `s'`. -/
lemma stalkAtMap_curvePullbackSubι (F : WeilSheaf k₀ l X)
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber} {n : ℕ}
    (hs' : s' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius L ^ n).asIso.hom ≫ s')
    (P : Subobject F.obj.carrier) (hP : (⇑F.frobeniusTwist)^[N] P = P)
    (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    stalkAtMap s' n hs' (curvePullbackSubι j hj F P hP hPl) =
      ((WeilCoefficients.toModuleCat l).map ((Sheaf.Γ _ _).map ((s')^*[WeilCoefficients.{u} l].map
        ((j)^*[WeilCoefficients.{u} l].map ((ProEtale.AdicSheaf.forget _).map P.arrow))))).hom :=
  rfl

omit [Finite L] [Fact (ringChar L ≠ l)] in
/-- The comparison of stalks along `Θ ≫ s = s' ≫ j` is natural in the subsheaf `P ⊆ F̄`. -/
lemma toModuleCat_map_comp_globalSectionsTransport_id (F : WeilSheaf k₀ l X)
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {Θ : Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    (hsq : Θ ≫ s = s' ≫ j) (P : Subobject F.obj.carrier) :
    ((WeilCoefficients.toModuleCat l).map ((Sheaf.Γ _ _).map ((s')^*[WeilCoefficients.{u} l].map
        ((j)^*[WeilCoefficients.{u} l].map ((ProEtale.AdicSheaf.forget _).map P.arrow))))).hom ∘ₗ
      ((WeilCoefficients.toModuleCat l).map (ProEtale.globalSectionsTransport _ hsq
        (𝟙 ((j)^*[WeilCoefficients.{u} l].obj (Subobject.underlying.obj P).X)))).hom =
    ((WeilCoefficients.toModuleCat l).map (ProEtale.globalSectionsTransport _ hsq
        (𝟙 ((j)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X)))).hom ∘ₗ
      ((WeilCoefficients.toModuleCat l).map ((Sheaf.Γ _ _).map ((s)^*[WeilCoefficients.{u} l].map
        ((ProEtale.AdicSheaf.forget _).map P.arrow)))).hom := by
  rw [← WeilCoefficients.toModuleCat_map_comp_hom, ← WeilCoefficients.toModuleCat_map_comp_hom]
  exact congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom)
    (ProEtale.globalSectionsTransport_id_naturality _ hsq
      ((ProEtale.AdicSheaf.forget _).map P.arrow))

omit [Finite L] [Fact (ringChar L ≠ l)] in
/-- The comparison of stalks along `Θ ≫ s = s' ≫ j`, for the identity of the underlying sheaf
`j^* F̄`, in terms of the algebra `AlgebraicGeometry.WeilSheaf.powIsoAlgebra`. -/
lemma globalSectionsTransport_id_powIsoAlgebra (F : WeilSheaf k₀ l X)
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {Θ : Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    (hsq : Θ ≫ s = s' ≫ j) :
    ProEtale.globalSectionsTransport _ hsq
        (𝟙 ((j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X)) =
      ProEtale.globalSectionsTransport _ hsq
        (𝟙 ((j)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X)) :=
  rfl

/-- The comparison of stalks `F_s ⟶ (j^* F̄)_{s'}` along `Θ ≫ s = s' ≫ j`, `Θ` an isomorphism,
carries the stalk `P_s` of a subsheaf `P` defined over `L` onto the image of the stalk of its
pullback. -/
lemma range_stalkAtMap_curvePullbackSubι (F : WeilSheaf k₀ l X)
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (Θ : Spec (.of (AlgebraicClosure L)) ≅ Spec (.of (AlgebraicClosure k₀)))
    (hsq : Θ.hom ≫ s = s' ≫ j) {n : ℕ}
    (hs' : s' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius L ^ n).asIso.hom ≫ s')
    (P : Subobject F.obj.carrier) (hP : (⇑F.frobeniusTwist)^[N] P = P)
    (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    LinearMap.range (stalkAtMap s' n hs' (curvePullbackSubι j hj F P hP hPl)) =
      (F.stalkSubspace s P).map ((WeilCoefficients.toModuleCat l).map
        (ProEtale.globalSectionsTransport _ hsq
          (𝟙 ((j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X)))).hom := by
  have : IsIso (ProEtale.globalSectionsTransport _ hsq
      (𝟙 ((j)^*[WeilCoefficients.{u} l].obj (Subobject.underlying.obj P).X))) :=
    ProEtale.isIso_globalSectionsTransport _ _ hsq _
  rw [stalkAtMap_curvePullbackSubι, stalkSubspace, ← LinearMap.range_comp,
    ← LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2
      ((ModuleCat.epi_iff_surjective ((WeilCoefficients.toModuleCat l).map
        (ProEtale.globalSectionsTransport _ hsq
          (𝟙 ((j)^*[WeilCoefficients.{u} l].obj (Subobject.underlying.obj P).X))))).1
        inferInstance)),
    toModuleCat_map_comp_globalSectionsTransport_id j F hsq P]
  rfl

/-- A geometric point `s` of `X̄` under a geometric point `s'` of `Ȳ` fixed by `Fr_Yⁿ` up to
reparametrisation, through `Spec θ : Spec k̄_L ≅ Spec k̄₀`, is fixed by `Fr^{N n}` up to
reparametrisation, `N = [L : k₀]`. -/
lemma comp_geometricGaloisFrobenius_pow_mul_of_comp_eq [Algebra k₀ L]
    (hj' : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ j)
    (hN : N = Module.finrank k₀ L) (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure L)
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hss' : s' ≫ j = (specAlgHomAlgebraicClosureIso θ).hom ≫ s) {n : ℕ}
    (hs' : s' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius L ^ n).asIso.hom ≫ s') :
    s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * n)).asIso.hom =
      (specGeometricFrobenius k₀ ^ (N * n)).asIso.hom ≫ s := by
  have hΘ : (specGeometricFrobenius L ^ n).asIso.hom ≫ (specAlgHomAlgebraicClosureIso θ).hom =
      (specAlgHomAlgebraicClosureIso θ).hom ≫ (specGeometricFrobenius k₀ ^ (N * n)).asIso.hom := by
    rw [hN, specAlgHomAlgebraicClosureIso_hom]
    exact specGeometricFrobenius_pow_hom_comp_spec_map_algHom θ n
  rw [← cancel_epi (specAlgHomAlgebraicClosureIso θ).hom, ← Category.assoc, ← hss',
    Category.assoc, comp_geometricGaloisFrobenius_pow_mul_eq j hj' n, ← Category.assoc, hs',
    Category.assoc, hss', ← Category.assoc, hΘ, Category.assoc]

variable [Algebra k₀ L] (hN : N = Module.finrank k₀ L)
  (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure L)

include hN in
/-- The comparison of stalks `F_s ⟶ (j^* F̄)_{s'}` along `Spec θ ≫ s = s' ≫ j` intertwines the
Frobenius of `F` relative to `𝔽_{q^{N n}}` and that of the curve pullback relative to `L_n`. -/
lemma toModuleCat_map_globalSectionsTransport_comp_frobeniusEnd_curvePullback
    (F : WeilSheaf k₀ l X)
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hsq : (specAlgHomAlgebraicClosureIso θ).hom ≫ s = s' ≫ j) {n : ℕ}
    (hs' : s' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius L ^ n).asIso.hom ≫ s')
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * n)).asIso.hom =
      (specGeometricFrobenius k₀ ^ (N * n)).asIso.hom ≫ s) :
    ((WeilCoefficients.toModuleCat l).map (ProEtale.globalSectionsTransport _ hsq
        (𝟙 _ : (j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X ⟶
          ((curvePullback j hj).obj F).obj.carrier.X))).hom ∘ₗ
      (F.stalkAt s (N * n) hs).frobeniusEnd =
    (((curvePullback j hj).obj F).stalkAt s' n hs').frobeniusEnd ∘ₗ
      ((WeilCoefficients.toModuleCat l).map (ProEtale.globalSectionsTransport _ hsq
        (𝟙 _ : (j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X ⟶
          ((curvePullback j hj).obj F).obj.carrier.X))).hom := by
  have : Module.Finite k₀ L := Module.Finite.of_finite
  have hΘ : (specGeometricFrobenius L ^ n).asIso.hom ≫ (specAlgHomAlgebraicClosureIso θ).hom =
      (specAlgHomAlgebraicClosureIso θ).hom ≫ (specGeometricFrobenius k₀ ^ (N * n)).asIso.hom := by
    rw [hN, specAlgHomAlgebraicClosureIso_hom]
    exact specGeometricFrobenius_pow_hom_comp_spec_map_algHom θ n
  rw [frobeniusEnd_stalkAt, frobeniusEnd_stalkAt,
    ← WeilCoefficients.toModuleCat_map_comp_hom, ← WeilCoefficients.toModuleCat_map_comp_hom]
  refine congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h₀ : (specGeometricFrobenius k₀ ^ 0).asIso.hom ≫ s =
        s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom := by
      rw [pow_zero, pow_zero]
      rfl
    rw [globalSectionsTransport_frobeniusPowStr_congr F (Nat.mul_zero N)
      (by rw [Nat.mul_zero]) hs.symm h₀, globalSectionsTransport_frobeniusPowStr_zero F
      (by rw [pow_zero]; rfl), globalSectionsTransport_frobeniusPowStr_zero _
      (by rw [pow_zero]; rfl), Category.id_comp, Category.comp_id]
  · exact globalSectionsTransport_frobeniusPowStr_comp_curvePullback j hj
      (hN ▸ Module.finrank_pos) F n hn hsq hsq hs.symm hs'.symm hΘ

include hN in
/-- **Stalks of the pullback.** Let `s'` be a geometric point of `Ȳ` fixed by `Fr_Yⁿ` up to
reparametrisation, lying over the geometric point `s` of `X̄` through `j` and the identification
`Spec θ : Spec k̄_L ≅ Spec k̄₀`. Then `s` is fixed by `Fr^{N n}` up to reparametrisation, and the
stalk of `curvePullback j hj F` at `s'`, with its Frobenius relative to `L_n`, is the stalk of `F`
at `s` with its Frobenius relative to `𝔽_{q^{N n}}`; the isomorphism carries the stalk of the
pullback of a subsheaf `P` defined over `L` onto the stalk `P_s`. -/
theorem exists_equiv_stalkAt_curvePullback (F : WeilSheaf k₀ l X)
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hss' : s' ≫ j = (specAlgHomAlgebraicClosureIso θ).hom ≫ s) {n : ℕ}
    (hs' : s' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius L ^ n).asIso.hom ≫ s') :
    ∃ (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * n)).asIso.hom =
        (specGeometricFrobenius k₀ ^ (N * n)).asIso.hom ≫ s)
      (e : (((curvePullback j hj).obj F).stalkAt s' n hs').Equiv (F.stalkAt s (N * n) hs)),
      ∀ (P : Subobject F.obj.carrier) (hP : (⇑F.frobeniusTwist)^[N] P = P)
        (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)),
        (LinearMap.range (stalkAtMap s' n hs' (curvePullbackSubι j hj F P hP hPl))).map
            e.toLinearEquiv.toLinearMap =
          F.stalkSubspace s P := by
  have hs := comp_geometricGaloisFrobenius_pow_mul_of_comp_eq j hj hN θ hss' hs'
  have hsq : (specAlgHomAlgebraicClosureIso θ).hom ≫ s = s' ≫ j := hss'.symm
  have : IsIso (ProEtale.globalSectionsTransport _ hsq
      (𝟙 ((j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X))) :=
    ProEtale.isIso_globalSectionsTransport _ _ hsq _
  let e : (F.stalkAt s (N * n) hs).Equiv (((curvePullback j hj).obj F).stalkAt s' n hs') :=
    .ofComp (WeilCoefficients.linearEquivOfIso (asIso (ProEtale.globalSectionsTransport _ hsq
      (𝟙 ((j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X)))))
      (by
        rw [WeilCoefficients.linearEquivOfIso_toLinearMap, asIso_hom]
        exact toModuleCat_map_globalSectionsTransport_comp_frobeniusEnd_curvePullback j hj hN θ F
          hsq hs' hs)
  refine ⟨hs, e.symm, fun P hP hPl ↦ ?_⟩
  rw [range_stalkAtMap_curvePullbackSubι j hj F _ hsq hs' P hP hPl,
    FrobeniusModule.Equiv.symm_toLinearEquiv, Submodule.map_symm_eq_iff]
  exact congrArg (fun f ↦ Submodule.map f (F.stalkSubspace s P))
    (WeilCoefficients.linearEquivOfIso_toLinearMap _)

include hN in
/-- The pullback of an `ι`-real Weil sheaf is `ι`-real: at a closed point of `Y` of degree `n`
over `L`, the local Frobenius of the pullback is, up to conjugation, a power of the local
Frobenius of `F` at the image point. -/
theorem IsReal.curvePullback [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of L))] {ι : PadicAlgCl l →+* ℂ}
    {F : WeilSheaf k₀ l X} (hF : F.IsReal ι) :
    ((WeilSheaf.curvePullback j hj).obj F).IsReal ι := by
  intro y
  have : Module.Finite k₀ L := Module.Finite.of_finite
  have hN₀ : N ≠ 0 := hN ▸ Module.finrank_pos.ne'
  let θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure L := IsAlgClosed.lift
  have hss' : (Y ↘ Spec (CommRingCat.of L)).geometricFiberPointOfFinitePoint y ≫ j =
      (specAlgHomAlgebraicClosureIso θ).hom ≫ (specAlgHomAlgebraicClosureIso θ).inv ≫
        (Y ↘ Spec (CommRingCat.of L)).geometricFiberPointOfFinitePoint y ≫ j := by
    rw [Iso.hom_inv_id_assoc]
  obtain ⟨hs, e, -⟩ := exists_equiv_stalkAt_curvePullback j hj hN θ F hss'
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ y)
  exact FrobeniusModule.IsReal.of_equiv e (hF.stalkAt _ (mul_ne_zero hN₀
    (Scheme.Hom.degreeOver_ne_zero _ y.2)) hs)

end WeilSheaf

end AlgebraicGeometry
