package collex

import (
	"sync"
)

type KeyTypeValueTypeKeyValue struct {
	Key   KeyType
	Value ValueType
}

type KeyTypeValueTypeConcurrentMapOption func(*KeyTypeValueTypeConcurrentMap)

func WithUnsafeKeyTypeValueTypeMap(m map[KeyType]ValueType) KeyTypeValueTypeConcurrentMapOption {
	return func(cm *KeyTypeValueTypeConcurrentMap) {
		if cm == nil {
			return
		}
		cm.m = m
	}
}

func WithKeyTypeValueTypeMap(m map[KeyType]ValueType) KeyTypeValueTypeConcurrentMapOption {
	return func(cm *KeyTypeValueTypeConcurrentMap) {
		if cm == nil || m == nil {
			return
		}
		cm.L.Lock()
		for k, v := range m {
			cm.m[k] = v
		}
		cm.L.Unlock()
	}
}

func NewKeyTypeValueTypeConcurrentMap(opts ...KeyTypeValueTypeConcurrentMapOption) *KeyTypeValueTypeConcurrentMap {
	cm := &KeyTypeValueTypeConcurrentMap{
		m: make(map[KeyType]ValueType),
		L: &sync.RWMutex{},
	}
	for _, opt := range opts {
		opt(cm)
	}
	return cm
}

type KeyTypeValueTypeMapKeyValue struct {
	Key   KeyType
	Value ValueType
}

type KeyTypeValueTypeConcurrentMap struct {
	m map[KeyType]ValueType
	L *sync.RWMutex
}

func (cm *KeyTypeValueTypeConcurrentMap) Get(k KeyType) ValueType {
	cm.L.RLock()
	defer cm.L.RUnlock()
	v := cm.m[k]
	return v
}
func (cm *KeyTypeValueTypeConcurrentMap) GetDefault(k KeyType, create func() (ValueType, error)) (ValueType, error) {
	var v ValueType
	var err error
	var ok bool
	cm.L.Lock()
	defer cm.L.Unlock()
	v, ok = cm.m[k]
	if ok {
		return v, nil
	}
	v, err = create()
	if err == nil {
		cm.m[k] = v
	}
	return v, err
}

func (cm *KeyTypeValueTypeConcurrentMap) GetOK(k KeyType) (ValueType, bool) {
	cm.L.RLock()
	defer cm.L.RUnlock()
	v, ok := cm.m[k]
	return v, ok
}

func (cm *KeyTypeValueTypeConcurrentMap) Set(k KeyType, v ValueType) {
	cm.L.Lock()
	defer cm.L.Unlock()
	cm.m[k] = v

}

func (cm *KeyTypeValueTypeConcurrentMap) Delete(k KeyType) (ValueType, bool) {
	cm.L.Lock()
	defer cm.L.Unlock()
	v, ok := cm.m[k]
	if ok {
		delete(cm.m, k)
	}
	return v, ok
}

func (cm *KeyTypeValueTypeConcurrentMap) SetKeyValues(kvs ...KeyTypeValueTypeKeyValue) {
	cm.L.Lock()
	defer cm.L.Unlock()
	for _, kv := range kvs {
		cm.m[kv.Key] = kv.Value
	}
}

func (cm *KeyTypeValueTypeConcurrentMap) Keys() []KeyType {
	cm.L.RLock()
	defer cm.L.RUnlock()
	var keys []KeyType
	for k := range cm.m {
		keys = append(keys, k)
	}
	return keys
}

func (cm *KeyTypeValueTypeConcurrentMap) Values() []ValueType {
	cm.L.RLock()
	defer cm.L.RUnlock()
	var values []ValueType
	for _, v := range cm.m {
		values = append(values, v)
	}
	return values
}

func (cm *KeyTypeValueTypeConcurrentMap) KeyValues() []KeyTypeValueTypeKeyValue {
	cm.L.RLock()
	defer cm.L.RUnlock()
	var pairs []KeyTypeValueTypeKeyValue
	for k, v := range cm.m {
		pairs = append(pairs, KeyTypeValueTypeKeyValue{Key: k, Value: v})
	}
	return pairs
}

func (cm *KeyTypeValueTypeConcurrentMap) ToUnsafeMap() map[KeyType]ValueType {
	cm.L.RLock()
	defer cm.L.RUnlock()
	m := make(map[KeyType]ValueType)
	for k, v := range cm.m {
		m[k] = v
	}
	return m
}
