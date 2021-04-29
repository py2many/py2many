package pygo

import (
	"reflect"
)

func Contains(s interface{}, element interface{}) bool {
	container := reflect.ValueOf(s)

	if container.Kind() == reflect.Slice {
		for i := 0; i < container.Len(); i++ {
			if container.Index(i).Interface() == element {
				return true
			}
		}
	}

	return false
}

func MapContains(m interface{}, element interface{}) bool {
	container := reflect.ValueOf(m)

	if container.Kind() == reflect.Map {
		return container.MapIndex(reflect.ValueOf(element)).IsValid()
	}

	return false
}
