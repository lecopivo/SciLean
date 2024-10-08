import SciLean.Data.DataArray.DataArray

namespace SciLean.DataArrayN


abbrev mapMono [IndexType I] [PlainDataType X]
    (x : DataArrayN X I) (f : X → X) :=
  ArrayType.mapMono f x


abbrev mapIdxMono [IndexType I] [PlainDataType X]
    (x : DataArrayN X I) (f : I → X → X) :=
  ArrayType.mapIdxMono f x


abbrev foldl [IndexType I] [PlainDataType X]
    (x : DataArrayN X I) (op : X → X → X) (init : X) :=
  IndexType.foldl (fun b i => op b x[i]) init


abbrev reduceD [IndexType I] [PlainDataType X]
    (x : DataArrayN X I) (f : X → X → X) (default : X):=
  IndexType.reduceD (fun i => x[i]) f default


abbrev reduce [IndexType I] [PlainDataType X] [Inhabited X]
    (x : DataArrayN X I) (f : X → X → X) :=
  IndexType.reduce (fun i => x[i]) f


abbrev max [IndexType I] [PlainDataType X] [Max X] [Inhabited X]
    (x : DataArrayN X I) : X :=
  IndexType.reduce (fun i : I => x[i]) (Max.max · ·)


abbrev min [IndexType I] [PlainDataType X] [Min X] [Inhabited X]
    (x : DataArrayN X I) : X :=
  IndexType.reduce (fun i : I => x[i]) (Min.min · ·)
