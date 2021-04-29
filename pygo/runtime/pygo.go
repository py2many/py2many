package pygo

import (
	"reflect"
)

func contains(s interface{}, element interface{}) bool {
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
