//go:generate go run github.com/noho-digital/genny -in ./type_slice.go -out type_slices_gen.go gen Type=Interface,bool,complex64,complex128
//go:generate go run github.com/noho-digital/genny -in ./number_slice.go -out number_slices_gen.go gen Number=byte,rune,uintptr,uint,uint8,uint16,uint32,uint64,int,int8,int16,int32,int64,float32,float64
//go:generate go run github.com/noho-digital/genny -in ./set.go -out sets_gen.go gen Type=Interface,byte,rune,uintptr,bool,uint,uint8,uint16,uint32,uint64,int,int8,int16,int32,int64,float32,float64,complex64,complex128
//go:generate go run github.com/noho-digital/genny -in ./concurrent_map.go -out concurrent_maps_gen.go gen "KeyType=byte,rune,uint,uint8,uint16,uint32,uint64,int,int8,int16,int32,int64,float32,float64,string ValueType=byte,rune,uint,uint8,uint16,Interface,uint32,uint64,int,int8,int16,int32,int64,float32,float64,Type,bool,string"
package collex
