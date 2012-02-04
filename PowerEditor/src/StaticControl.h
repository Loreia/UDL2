//this file is part of notepad++
//Copyright (C)2003 Don HO ( donho@altern.org )
//
//This program is free software; you can redistribute it and/or
//modify it under the terms of the GNU General Public License
//as published by the Free Software Foundation; either
//version 2 of the License, or (at your option) any later version.
//
//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU General Public License for more details.
//
//You should have received a copy of the GNU General Public License
//along with this program; if not, write to the Free Software
//Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


#ifndef STATIC_CONTROL_H
#define STATIC_CONTROL_H

#include "Window.h"
class StaticControl : public Window
{
public :
	StaticControl() : Window() {};
	~StaticControl(){};
	void init(HINSTANCE hInst, HWND parent, int ctrlID) {
		Window::init(hInst, parent);
		//_hSelf = CreateDialog(hInstance, MAKEINTRESOURCE(IDD_LUNA_DIALOG), NULL, cryptoGUI_dlgProc);
	};

}

#endif //STATIC_CONTROL_H