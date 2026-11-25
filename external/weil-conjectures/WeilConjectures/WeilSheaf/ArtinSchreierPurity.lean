/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PointCount
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.WeilSheaf.ArtinSchreierTrace
public import WeilConjectures.WeilSheaf.StalkUpperStarCharpoly

/-!
# The local Frobenius of the Artin–Schreier sheaves

Let `k₀` be a finite field and `ψ` an additive character of `k₀` with values in `ℚ̄_ℓ`. The
Artin–Schreier sheaf `ℒ_{ψ(a x)}` (`AlgebraicGeometry.artinSchreier`) has one-dimensional
stalks: after pullback along the Artin–Schreier cover `ĀS` the `ψ`-isotypic component `ℒ_ψ` of
`AS_* ℚ̄_ℓ` becomes `ℚ̄_ℓ`, and every geometric point of the line lifts through the étale
surjection `ĀS`. Its local Frobenius at a closed point `x` is therefore the scalar given by its
trace, the value `ψ(Tr(a x))` of the trace function
(`AlgebraicGeometry.WeilSheaf.traceFunction_artinSchreier`), a root of unity. In particular
`ℒ_{ψ(a x)}` is punctually `ι`-pure of weight zero, and so is the Fourier kernel `μ^* ℒ_ψ`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.finrank_stalk_artinSchreier`: the stalks of `ℒ_{ψ(a x)}` are
  lines.
- `AlgebraicGeometry.WeilSheaf.exists_frobeniusEnd_stalk_artinSchreier`: at a closed point `x`
  the local Frobenius of `ℒ_{ψ(a x)}` is multiplication by `ψ(c)` for some `c ∈ k₀` which does
  not depend on `ψ`.
- `AlgebraicGeometry.isPunctuallyPureOfWeight_artinSchreier` (blueprint:
`lemma-artin-schreier-character-sheaf--7`):
  `ℒ_{ψ(a x)}` is punctually `ι`-pure of weight zero.
- `AlgebraicGeometry.isPunctuallyPureOfWeight_fourierKernel`: so is the Fourier kernel.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

open scoped ProEtale

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The global sections of a free `ℓ`-adic sheaf `ℚ̄_ℓⁿ` on the spectrum of a field form an
`n`-dimensional `ℚ̄_ℓ`-vector space. -/
lemma finrank_globalSections_of_iso_biproduct {K : Type u} [Field K]
    {M : AdicSheaf l (Spec (.of K))} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K))) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj M.X)) =
      n := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let G := Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l) ⋙
    WeilCoefficients.toModuleCat l
  let e' : G.obj M.X ≅ ModuleCat.of _ (Fin n → G.obj (adicConstantSheaf l (Spec (.of K)))) :=
    G.mapIso ((AdicSheaf.forget _).mapIso e ≪≫
      (AdicSheaf.forget _).mapBiproduct (fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K)))) ≪≫
      G.mapBiproduct (fun _ : Fin n ↦ adicConstantSheaf l (Spec (.of K))) ≪≫
      ModuleCat.biproductIsoPi (fun _ : Fin n ↦ G.obj (adicConstantSheaf l (Spec (.of K))))
  have : FiniteDimensional (PadicAlgCl l) (G.obj (adicConstantSheaf l (Spec (.of K)))) :=
    finiteDimensional_globalSections_adicConstantSheaf K
  have h1 : Module.finrank (PadicAlgCl l) (G.obj (adicConstantSheaf l (Spec (.of K)))) = 1 :=
    finrank_globalSections_adicConstantSheaf _
  refine e'.toLinearEquiv.finrank_eq.trans ?_
  simp [Module.finrank_pi_fintype, h1]

end ProEtale

/-- An endomorphism of a line is multiplication by its trace. -/
lemma _root_.LinearMap.eq_trace_smul_id_of_finrank_eq_one {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (h : Module.finrank K V = 1)
    (f : V →ₗ[K] V) : f = LinearMap.trace K V f • LinearMap.id := by
  obtain ⟨c, rfl, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h f
  rw [map_smul, LinearMap.trace_id, h, Nat.cast_one, smul_eq_mul, mul_one]

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

-- Instance search for the (co)kernels in the category of sheaves of modules is slow.
/-- After pullback along the Artin–Schreier cover `ĀS`, the `ψ`-isotypic component `ℒ_ψ` of
`AS_* ℚ̄_ℓ` becomes the constant sheaf `ℚ̄_ℓ`: the projector `e_ψ` factors there as averaging
followed by splitting (see `AlgebraicGeometry.WeilSheaf.isLisse_image_artinSchreierIdempotent`).
-/
lemma affineLine.nonempty_adicUpperStar_image_artinSchreierIdempotent_iso
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty ((ĀS)^*ᵃ[l].obj (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier ≅
      ⨁ fun _ : Fin 1 ↦ ProEtale.AdicSheaf.unit l
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  let Φ := ObjectProperty.ι (WeilSheaf.objectProperty k₀ l (affineLine k₀)) ⋙
    IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀))
  have := ObjectProperty.preservesKernels_ι _ (cokernel.π (WeilSheaf.artinSchreierIdempotent ψ))
  have := ObjectProperty.preservesCokernels_ι _ (WeilSheaf.artinSchreierIdempotent ψ)
  have : HasColimitsOfShape WalkingParallelPair
      (ProEtale.AdicSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    inferInstance
  have : HasLimitsOfShape WalkingParallelPair
      (ProEtale.AdicSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    inferInstance
  have hfac := affineLine.artinSchreierAverageModHom_splitModHom_of_restriction ψ
    (Φ.map (WeilSheaf.artinSchreierIdempotent ψ))
    (affineLine.restriction_map_artinSchreierIdempotent ψ)
  have hab := affineLine.artinSchreierSplitModHom_averageModHom (l := l) ψ
  have : IsSplitEpi (affineLine.artinSchreierAverageModHom l ψ) := ⟨⟨_, hab⟩⟩
  have : IsSplitMono (affineLine.artinSchreierSplitModHom l ψ) := ⟨⟨_, hab⟩⟩
  exact ⟨(ĀS)^*ᵃ[l].mapIso (Φ.mapIso (Abelian.imageIsoImage _).symm ≪≫
    Abelian.PreservesImage.iso Φ _ ≪≫ Abelian.imageIsoImage _) ≪≫
    ((ĀS)^*ᵃ[l].mapIso (Abelian.imageIsoImage _).symm ≪≫
    Abelian.PreservesImage.iso _ _ ≪≫ Abelian.imageIsoImage _) ≪≫
      (image.isoStrongEpiMono _ _ hfac).symm ≪≫
      (biproduct.isoProduct (fun _ : Fin 1 ↦ ProEtale.AdicSheaf.unit l
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≪≫ productUniqueIso _).symm⟩

namespace WeilSheaf

/-- The stalks of the `ψ`-isotypic component `ℒ_ψ` of `AS_* ℚ̄_ℓ` at all geometric points are
lines: the geometric point lifts through the étale surjection `ĀS`, after pullback along which
`ℒ_ψ` becomes `ℚ̄_ℓ`. -/
lemma finrank_stalkObj_image_artinSchreierIdempotent (ψ : AddChar k₀ (PadicAlgCl l))
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((image (artinSchreierIdempotent ψ)).stalkObj s)) = 1 := by
  obtain ⟨t, rfl⟩ := ProEtale.exists_comp_eq_of_weaklyEtale ĀS s
    ((affineLine.geometricArtinSchreierMap k₀).surjective _)
  obtain ⟨e⟩ := affineLine.nonempty_adicUpperStar_image_artinSchreierIdempotent_iso (l := l) ψ
  obtain ⟨e'⟩ := ProEtale.nonempty_upperStar_iso_biproduct t
    ⟨ProEtale.adicUpperStarUnitIso l t⟩ e
  refine ((WeilCoefficients.linearEquivOfIso ((Sheaf.Γ _ _).mapIso
    ((ProEtale.upperStarComp _ t ĀS).app _))).finrank_eq).trans ?_
  exact ProEtale.finrank_globalSections_of_iso_biproduct e'

section UpperStar

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- The stalks of a pullback have the dimensions of the stalks below. -/
theorem finrank_stalk_upperStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l Y) (z : X.finitePoints) :
    Module.finrank (PadicAlgCl l) (((upperStar φ).obj F).stalk z).carrier =
      Module.finrank (PadicAlgCl l)
        (F.stalk ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩).carrier := by
  rw [← LinearMap.charpoly_natDegree, charpoly_frobeniusEnd_stalk_upperStar,
    LinearMap.charpoly_natDegree]

end UpperStar

/-- The stalks of the Artin–Schreier sheaf `ℒ_{ψ(a x)}` are lines. -/
theorem finrank_stalk_artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀)
    (x : (affineLine k₀).finitePoints) :
    Module.finrank (PadicAlgCl l) ((artinSchreier ψ a).stalk x).carrier = 1 :=
  (finrank_stalk_upperStar _ _ x).trans (finrank_stalkObj_image_artinSchreierIdempotent ψ _)

/-- **The local Frobenius of an Artin–Schreier sheaf.** At a closed point `x` of the line, the
local Frobenius of `ℒ_{ψ(a x)}` is multiplication by `ψ(c)`, for some `c ∈ k₀` which does not
depend on `ψ`: the stalk is a line, so the Frobenius is multiplication by its trace, the value
`ψ(Tr(a x))` of the trace function at an `𝔽_{q^d}`-point over `x`, `d = [κ(x) : k₀]`
(`AlgebraicGeometry.WeilSheaf.traceFunction_artinSchreier`). -/
theorem exists_frobeniusEnd_stalk_artinSchreier (a : k₀) (x : (affineLine k₀).finitePoints) :
    ∃ c : k₀, ∀ ψ : AddChar k₀ (PadicAlgCl l),
      ((artinSchreier ψ a).stalk x).frobeniusEnd = ψ c • LinearMap.id := by
  set f := affineLine k₀ ↘ Spec (CommRingCat.of k₀)
  set d := f.degreeOver x.1
  have hd : d ≠ 0 := Scheme.Hom.degreeOver_ne_zero _ x.2
  have : Finite (FiniteField.galoisExtension k₀ d) := Module.finite_of_finite k₀
  -- an `𝔽_{q^d}`-rational point over `x`
  obtain ⟨y, hy⟩ : ∃ y : f.fieldPoints (FiniteField.galoisExtension k₀ d),
      y.1.base (IsLocalRing.closedPoint _) = x.1 := by
    let := (f.residueFieldAlgebraMap x.1).toAlgebra
    obtain ⟨ψ⟩ : Nonempty ((affineLine k₀).residueField x.1 →ₐ[k₀]
        FiniteField.galoisExtension k₀ d) := by
      rw [FiniteField.nonempty_algHom_iff_finrank_dvd, FiniteField.finrank_galoisExtension k₀ d hd]
      exact dvd_rfl
    obtain ⟨y, hy⟩ := (f.exists_fieldPoints_base_eq_iff _ x.1).2
      ⟨CommRingCat.ofHom ψ.toRingHom, ψ.comp_algebraMap⟩
    exact ⟨y, (congrArg y.1.base (Subsingleton.elim _ _)).trans hy⟩
  refine ⟨Algebra.trace k₀ (FiniteField.galoisExtension k₀ d)
    (algebraMap k₀ _ a * (Scheme.ΓSpecIso (.of _)).hom.hom
      (y.1.appTop (AffineSpace.coord _ PUnit.unit))), fun ψ ↦ ?_⟩
  have h := traceFunction_eq_trace_frobeniusEnd_stalk_pow (artinSchreier ψ a) d y x hy
  rw [Nat.div_self (Nat.pos_of_ne_zero hd), pow_one, traceFunction_artinSchreier ψ a hd y] at h
  rw [h]
  exact LinearMap.eq_trace_smul_id_of_finrank_eq_one (finrank_stalk_artinSchreier ψ a x) _

end WeilSheaf

/-- The values of an additive character of a finite field are roots of unity, of modulus one
under any embedding into `ℂ`. -/
lemma AddChar.norm_map_apply_eq_one {K : Type*} [Field K] [Finite K] {R : Type*} [CommRing R]
    (ψ : AddChar K R) (ι : R →+* ℂ) (c : K) : ‖ι (ψ c)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := ringChar K) ?_
    (CharP.char_ne_zero_of_finite K _)
  rw [← map_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul,
    AddChar.map_zero_eq_one, map_one]

/-- **Purity of the Artin–Schreier sheaf.** The Artin–Schreier sheaf `ℒ_{ψ(a x)}` on the affine
line is punctually `ι`-pure of weight zero: at every closed point its local Frobenius is
multiplication by a value of `ψ`, a root of unity
(`AlgebraicGeometry.WeilSheaf.exists_frobeniusEnd_stalk_artinSchreier`).
(blueprint: `lemma-artin-schreier-character-sheaf--7`) -/
theorem isPunctuallyPureOfWeight_artinSchreier (ι : PadicAlgCl l →+* ℂ)
    (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    (artinSchreier ψ a).IsPunctuallyPureOfWeight ι 0 := by
  intro x α hα
  obtain ⟨c, hc⟩ := WeilSheaf.exists_frobeniusEnd_stalk_artinSchreier (l := l) a x
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, hc ψ,
    LinearMap.smul_apply, LinearMap.id_apply] at hv
  have hαc : α = ψ c := (smul_left_injective _ hv.2 hv.1).symm
  rw [hαc, AddChar.norm_map_apply_eq_one ψ ι c, zero_div, Real.rpow_zero]

/-- The Fourier kernel `μ^* ℒ_ψ` is punctually `ι`-pure of weight zero, as a pullback of the
Artin–Schreier sheaf `ℒ_ψ`. -/
theorem isPunctuallyPureOfWeight_fourierKernel (ι : PadicAlgCl l →+* ℂ)
    (ψ : AddChar k₀ (PadicAlgCl l)) : (fourierKernel ψ).IsPunctuallyPureOfWeight ι 0 :=
  (isPunctuallyPureOfWeight_artinSchreier ι ψ 1).upperStar _

end AlgebraicGeometry
